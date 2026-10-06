import ProofLadders.Common.Symmetric
import ProofLadders.Common.Functional
import ConstructiveCryptography.Tactics.Substitution

/-!
# Two-block CBC-MAC

The fourth problem of the symmetric ladder [1, §4]: if `F : K → X → X` is a secure PRF on a
finite commutative group `X` of blocks, with keys in a finite set `K`, then two-block CBC-MAC

$$F^2_{\mathsf{cbc}}(k, x_1 \,\|\, x_2) = F(k, F(k, x_1) \oplus x_2)$$

is a secure PRF on `X × X`, with `⊕` the group addition. The notes' input and output length
`λ`, keys and blocks in `{0,1}^λ` with `⊕` the XOR, is the instance `K = X = Bits λ`
(`cbc_mac_2_bits`).

The proof swaps `F` for a lazy random dictionary `R`, after which the construction is
`R(R(x₁) ⊕ x₂)` under a uniform round function, `roundURF`. It is the uniform random function
until a round input repeats: the second-call input `R(x₁) ⊕ x₂` of a message equals the
second-call input of another message or the first block `x₁'` of any message. This covers the
bad event of [1, §4], that `R[y₁ ⊕ x₂]` is already defined. As a game (`cbc2_game_equiv`), its
blind winning probability is at most `q(3q-1)/(2|X|)` (`cbc2Game_blind_bound`), which bounds
the distance (`roundURF_distance_le`). The swap is the PRF assumption at `2q` queries, since the
construction calls `F` twice per message. At `X = Bits λ` the bound is `q(3q-1)/2^{λ+1}`.

The condition also counts second-call inputs equal to later first blocks, which the factorization
through the uniform random function requires, hence `q(3q-1)/(2|X|)`. On a single query it has
probability `1/|X|`, which is `2^{-λ}` at `{0,1}^λ` (`roundCollision_single`,
`roundCollision_single_bits`).

Style: the swap is a substitution through a converter; the collision step is bounded by
conditional equivalence, on a sampled function with a hidden condition.

## Main definitions

* `cbcMAC₂ F`: two-block CBC-MAC
* `roundURF X`: `R(R(x₁) ⊕ x₂)` under a uniform round function `R`
* `RoundCollision`, `cbc2Game X`: the bad event, and the collision game
* `cbc₂ X`, `cbc₂.perPortBound X`: CBC on two blocks, and its typing at per-port budgets

## Main results

* `cbc2_game_equiv`, `cbc2Game_blind_bound`, `roundURF_distance_le`: the collision step
* `roundCollision_single`, `roundCollision_single_bits`: on one query the condition has
  probability `1/|X|`, which is `2^{-λ}` at `{0,1}^λ`
* `cbc_mac_2`: two-block CBC-MAC is a secure PRF, with the reduction `cbc₂`
* `cbc_mac_2_bits`: the same at `{0,1}^λ`
* `cbc₂_smul_ofFunction`, `cbc₂_smul_prfReal`, `cbc₂_smul_urf`: `cbc₂` on sampled functions

## References

1. The symmetric proof ladder, *Security proofs in the style of The Joy of Cryptography*,
   `proof-ladders/symmetric-ladder`, `Notes/selfcontained.tex`.
-/

namespace ProofLadders.CBCMAC

open Commons Probability SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface
open scoped SystemAlgebra SystemAlgebra.DSL

noncomputable section

variable {K X : Type} [AddCommGroup X]

/-- **Two-block CBC-MAC** [1, §4]: `y₁ := F(k, x₁)`, `y₂ := F(k, y₁ ⊕ x₂)`, return `y₂`. -/
def cbcMAC₂ (F : K → X → X) (k : K) (x : X × X) : X :=
  F k (F k x.1 + x.2)

/-- **A repeated round input**: the second-call input of a queried message equals the
second-call input of a different queried message, or the first block of a queried message. -/
def RoundCollision (R : X → X) (xs : List (X × X)) : Prop :=
  (∃ x ∈ xs, ∃ x' ∈ xs, x ≠ x' ∧ R x.1 + x.2 = R x'.1 + x'.2) ∨
    ∃ x ∈ xs, ∃ x' ∈ xs, R x.1 + x.2 = x'.1

lemma roundCollision_monotone (R : X → X) {xs xs' : List (X × X)} (hp : xs <+: xs') :
    RoundCollision R xs → RoundCollision R xs'
  | .inl ⟨x, hx, x', hx', distinct, equal⟩ =>
    .inl ⟨x, hp.subset hx, x', hp.subset hx', distinct, equal⟩
  | .inr ⟨x, hx, x', hx', equal⟩ => .inr ⟨x, hp.subset hx, x', hp.subset hx', equal⟩

variable (X) [Fintype X] [DecidableEq X]

/-- The interface of two-block messages: inputs in `X × X`, outputs in `X`, at most `q`
queries. -/
abbrev Messages (q : Evaluation.Port → ℕ) : Interface :=
  Evaluation.perPort (X × X) X q

/-- **CBC-MAC under a uniform round function**: `R(R(x₁) ⊕ x₂)` for a uniformly random
`R : X → X`. -/
def roundURF {q : Evaluation.Port → ℕ} : Resource (Messages X q) :=
  Resource.sample (Distribution.uniform (X → X))
    fun R => Resource.ofFunction fun _ x => R (R x.1 + x.2)

/-- **The collision game**: the uniform round function, with the hidden condition
`RoundCollision`. -/
def cbc2Game (q : Evaluation.Port → ℕ) :=
  PDG.ofSingleFunction (Messages X q).domain (Messages X q).nonempty_prefix
    (Messages X q).bound (Messages X q).length_le
    (Distribution.uniform (X → X)) (fun R x => R (R x.1 + x.2))
    (fun R => ⟨RoundCollision R, fun {_ _} hp => roundCollision_monotone R hp⟩)

/-- Without the bad event, the outputs are values of `R` at distinct points outside the first
blocks, so they have the law of the uniform random function. -/
lemma cbc2_game_equiv (q : Evaluation.Port → ℕ) :
    cbc2Game X q |≡ URF (Messages X q) := by
  classical
  rw [URF_perPort_eq (X × X) X]
  apply PDG.ofSingleFunction_gameEquivalent
  intro xs answers
  have ideal := Counting.uniform_mass_apply_list_eq (Y := X) xs id (Set.injOn_id _) answers
  simp only [id] at ideal
  dsimp only
  rw [ideal, ← Fintype.card_coe xs.toFinset]
  -- Given `R` on the first blocks, which determines the condition, the second-call inputs are
  -- distinct and outside the first blocks, and the values of `R` there are uniform.
  rw [← Counting.uniform_mass_fresh_eq (ι := xs.toFinset) {y₁ | ∃ x ∈ xs, x.1 = y₁}
    (fun R => ¬ RoundCollision R xs) (fun R x => R x.1.1 + x.1.2) ?_ ?_ ?_
    (fun x => answers x.1)]
  · refine Distribution.mass_congr _ fun R => and_congr_left fun _ =>
      ⟨fun h => funext fun x => h x.1 (List.mem_toFinset.mp x.2),
        fun h x hx => congrFun h ⟨x, List.mem_toFinset.mpr hx⟩⟩
  · intro R R' hR
    have hR' : ∀ x ∈ xs, R x.1 = R' x.1 := fun x hx => hR x.1 ⟨x, hx, rfl⟩
    simp only [RoundCollision]
    constructor <;> rintro h (⟨x, hx, x', hx', hne, he⟩ | ⟨x, hx, x', hx', he⟩)
    · exact h (.inl ⟨x, hx, x', hx', hne, by rw [hR' x hx, hR' x' hx', he]⟩)
    · exact h (.inr ⟨x, hx, x', hx', by rw [hR' x hx, he]⟩)
    · exact h (.inl ⟨x, hx, x', hx', hne, by rw [← hR' x hx, ← hR' x' hx', he]⟩)
    · exact h (.inr ⟨x, hx, x', hx', by rw [← hR' x hx, he]⟩)
  · intro R R' hR
    funext x
    rw [hR x.1.1 ⟨x.1, List.mem_toFinset.mp x.2, rfl⟩]
  · intro R hR
    refine ⟨fun x x' h => Subtype.ext (by_contra fun hne => hR (.inl ⟨x.1,
      List.mem_toFinset.mp x.2, x'.1, List.mem_toFinset.mp x'.2, hne, h⟩)), ?_⟩
    rintro x ⟨x', hx', he⟩
    exact hR (.inr ⟨x.1, List.mem_toFinset.mp x.2, x', hx', he.symm⟩)

/-- Blind winning is the bad event on at most `q` fixed messages: `q(q-1)/2` pairs of second-call
inputs and `q²` pairs of a second-call input and a first block. -/
lemma cbc2Game_blind_bound (q : Evaluation.Port → ℕ) :
    ν((cbc2Game X q).blind (Messages X q).nonempty_prefix) ≤
      (q .eval : ℝ) * (3 * (q .eval : ℝ) - 1) / (2 * Fintype.card X) := by
  have hq : 0 ≤ (q .eval : ℝ) * (3 * (q .eval : ℝ) - 1) := by
    simpa using natCast_mul_sub_one_le (Nat.zero_le (q .eval)) (by norm_num : (1 : ℝ) ≤ 3)
  apply PDG.ofFunction_blind_le (div_nonneg hq (by positivity))
  intro xs hxs
  let S := (xs.map Sigma.snd).toFinset
  have hS : S.card ≤ q .eval :=
    (List.toFinset_card_le _).trans ((List.length_map _).trans_le (evaluation_length_le hxs))
  change (Distribution.uniform (X → X)).mass
    (fun R => RoundCollision R (xs.map Sigma.snd)) ≤ _
  -- A union bound; each event fixes one value of `R` at a first block, of probability `1/|X|`.
  have pairs : (Distribution.uniform (X → X)).mass
      (fun R => ∃ x ∈ xs.map Sigma.snd, ∃ x' ∈ xs.map Sigma.snd, x ≠ x' ∧
        R x.1 + x.2 = R x'.1 + x'.2) ≤ S.card * (S.card - 1) / 2 * (1 / Fintype.card X) := by
    calc _ = (Distribution.uniform (X → X)).mass
          (fun R => ∃ x ∈ S, ∃ x' ∈ S, x ≠ x' ∧ R x.1 + x.2 = R x'.1 + x'.2) :=
          Distribution.mass_congr _ fun R => by simp [S]
      _ ≤ _ := by
          refine Distribution.mass_exists_pair_le Distribution.uniform_nonNeg S _
            (fun _ _ _ h => h.symm) fun x _ x' _ h => ?_
          by_cases h₁ : x.1 = x'.1
          · -- Messages with one first block differ in the second, so their inputs differ.
            rw [Distribution.mass_eq_zero_of_forall_not _ fun R hR => h (Prod.ext h₁
              (by rw [h₁] at hR; exact add_left_cancel hR))]
            positivity
          · exact Counting.uniform_mass_coord_determined_le x.1 (· + x.2)
              (add_left_injective x.2) (fun R => R x'.1 + x'.2)
              (fun _ _ hR => by rw [hR x'.1 (Ne.symm h₁)])
  have blocks : (Distribution.uniform (X → X)).mass
      (fun R => ∃ x ∈ xs.map Sigma.snd, ∃ x' ∈ xs.map Sigma.snd, R x.1 + x.2 = x'.1) ≤
        S.card * (S.card * (1 / Fintype.card X)) := by
    calc _ = (Distribution.uniform (X → X)).mass
          (fun R => ∃ x ∈ S, ∃ x' ∈ S, R x.1 + x.2 = x'.1) :=
          Distribution.mass_congr _ fun R => by simp [S]
      _ ≤ ∑ x ∈ S, (Distribution.uniform (X → X)).mass
          (fun R => ∃ x' ∈ S, R x.1 + x.2 = x'.1) :=
          Distribution.mass_exists_le Distribution.uniform_nonNeg _ _
      _ ≤ ∑ x ∈ S, ∑ x' ∈ S, (Distribution.uniform (X → X)).mass
          (fun R => R x.1 + x.2 = x'.1) :=
          Finset.sum_le_sum fun _ _ => Distribution.mass_exists_le Distribution.uniform_nonNeg _ _
      _ ≤ ∑ x ∈ S, ∑ x' ∈ S, (1 / Fintype.card X : ℝ) :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ =>
            Counting.uniform_mass_coord_determined_le x.1 (· + x.2) (add_left_injective x.2)
              (fun _ => x'.1) (fun _ _ _ => rfl)
      _ = _ := by simp
  refine ((Distribution.mass_or_le Distribution.uniform_nonNeg _ _).trans
    (add_le_add pairs blocks)).trans ?_
  have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc _ = (S.card : ℝ) * (3 * S.card - 1) / (2 * Fintype.card X) := by field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right
        (natCast_mul_sub_one_le hS (by norm_num : (1 : ℝ) ≤ 3)) (by positivity)

variable {X}

/-- **One message meets the condition with probability `1/|X|`**: on a single query the
condition, which is then the bad event of [1, §4], is `R(x₁) ⊕ x₂ = x₁`. -/
theorem roundCollision_single (x : X × X) :
    (Distribution.uniform (X → X)).mass (fun R => RoundCollision R [x]) =
      1 / Fintype.card X := by
  have h : ∀ R : X → X, RoundCollision R [x] ↔ R x.1 = x.1 - x.2 := by
    intro R
    simp only [RoundCollision, List.mem_singleton, exists_eq_left, ne_eq, not_true_eq_false,
      false_and, false_or]
    exact ⟨eq_sub_of_add_eq, fun h => by rw [h, sub_add_cancel]⟩
  rw [Distribution.mass_congr _ h]
  have := Counting.uniform_mass_apply_list_eq (Y := X) [x.1] id (Set.injOn_id _)
    fun _ => x.1 - x.2
  simp only [List.mem_singleton, forall_eq, id, List.toFinset_cons, List.toFinset_nil,
    insert_empty_eq, Finset.card_singleton, pow_one] at this
  exact this

/-- **One message meets the condition with probability `2^{-λ}`** at `{0,1}^λ`. -/
lemma roundCollision_single_bits {secpar : ℕ} (x : Bits secpar × Bits secpar) :
    (Distribution.uniform (Bits secpar → Bits secpar)).mass (fun R => RoundCollision R [x]) =
      1 / 2 ^ secpar := by
  simpa only [card_bits, Nat.cast_pow, Nat.cast_ofNat] using roundCollision_single x

variable (X)

/-- **The collision step**: CBC-MAC under a uniform round function is within `q(3q-1)/(2|X|)`
of the uniform random function on two-block messages. -/
lemma roundURF_distance_le (q : Evaluation.Port → ℕ) :
    Δ (roundURF X (q := q)) (URF (Messages X q)) ≤
      ENNReal.ofReal ((q .eval : ℝ) * (3 * (q .eval : ℝ) - 1) / (2 * Fintype.card X)) :=
  ((cbc2_game_equiv X q).game_dist_ofSingleFunction_le rfl).trans
    (ENNReal.ofReal_le_ofReal (cbc2Game_blind_bound X q))

/-! ## Sampled functions

The reduction of the swap is CBC on two blocks, `cbc₂`, a converter without state that makes
its two calls per message. The DSL types it by a total budget; `cbc₂.perPortBound` is the same
program at per-port budgets, `q` messages into `2q` calls. On a function `f` it computes
`f(f(x₁) ⊕ x₂)`, so on `prf-real^F` it is `prf-real^{cbc-2}` and on the uniform random function
it is `roundURF`; with the collision step this gives `cbc_mac_2`, with `cbc₂` as its
reduction. -/

end

-- `cbc₂`: `y₁ ← prf.query(x₁)`, `y₂ ← prf.query(y₁ ⊕ x₂)`, return `y₂`.
converter cbc₂(X : Type) [Fintype X] [AddCommGroup X] : Evaluation (X × X) X
  inside prf : Evaluation X X
  on eval(x : X × X) → X
    y₁ ← prf.eval(x.1)
    y₂ ← prf.eval(y₁ + x.2)
    return y₂

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] (X : Type) [Fintype X] [AddCommGroup X]

/-- **`cbc₂` at per-port budgets**: `q` messages make at most `cbc₂.bound = 2` calls each. -/
def cbc₂.perPortBound (q : Evaluation.Port → ℕ) :
    Messages X q ⟶ Evaluation.perPort X X (fun _ => cbc₂.bound X * q .eval) :=
  Interface.Converter.ofProgramPerPort none (cbc₂.body X) (cbc₂.bound_spec X) q
    (q .eval) (Fintype.sum_unique q).le

variable {X}

/-- **`cbc₂` on a function** `f` is two-block CBC-MAC under the round function `f`. -/
lemma cbc₂_smul_ofFunction (q : Evaluation.Port → ℕ) (f : X → X) :
    cbc₂.perPortBound X q • Resource.ofFunction (fun _ => f) =
      Resource.ofFunction (A := Messages X q) fun _ x => f (f x.1 + x.2) := by
  unfold cbc₂.perPortBound Interface.Converter.ofProgramPerPort Interface.Converter.ofProgram
  refine Interface.ofDDC_ofProgramOn_smul_ofFunction (A := Messages X q)
    (B := Evaluation.perPort X X (fun _ => cbc₂.bound X * q .eval))
    none (cbc₂.body X) (cbc₂.bound_spec X) _ (fun _ => f) _ fun t o x => ?_
  -- Against `f`, every invocation makes its two calls and returns `f(f(x₁) ⊕ x₂)`.
  cases o
  refine ⟨some (), ?_⟩
  cases t <;> simp [Program.answer, cbc₂.body, callProg, returnProg]

/-- **`cbc₂` on `prf-real^F`** is `prf-real^{cbc-2}`. -/
lemma cbc₂_smul_prfReal (F : K → X → X) (q : Evaluation.Port → ℕ) :
    cbc₂.perPortBound X q • PRF.Real F = PRF.Real (cbcMAC₂ F) := by
  unfold PRF.Real
  rw [Resource.smul_sample]
  congr 1
  funext k
  exact cbc₂_smul_ofFunction q (F k)

variable [DecidableEq X]

variable (X) in
/-- **`cbc₂` on the uniform random function** is CBC-MAC under a uniform round function. -/
lemma cbc₂_smul_urf (q : Evaluation.Port → ℕ) :
    cbc₂.perPortBound X q • URF (Evaluation.perPort X X (fun _ => cbc₂.bound X * q .eval)) =
      roundURF X := by
  rw [URF_perPort_eq X X, Resource.smul_sample]
  congr 1
  funext R
  exact cbc₂_smul_ofFunction q R

/-- **Two-block CBC-MAC** [1, §4]: if `F` is a secure PRF within `ε` at `2q` queries, then
two-block CBC-MAC is a secure PRF at `q` queries within `ε` at the distinguishers with the
reduction `cbc₂` absorbed and the collision bound `q(3q-1)/(2|X|)`. -/
theorem cbc_mac_2 [AdmissibleDistinguishers] (F : K → X → X) (q : Evaluation.Port → ℕ)
    (ε : (Evaluation.perPort X X
      (fun _ => cbc₂.bound X * q .eval)).inputDomain.DistinguisherBehavior → ENNReal)
    (secure : PRF.Secure F ε) :
    PRF.Secure (cbcMAC₂ F) fun D => ε (absorb (cbc₂.perPortBound X q) D) +
      ENNReal.ofReal ((q .eval : ℝ) * (3 * (q .eval : ℝ) - 1) / (2 * Fintype.card X)) := by
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    PRF.Real (cbcMAC₂ F) = cbc₂.perPortBound X q • PRF.Real F := (cbc₂_smul_prfReal F q).symm
    _ ≃[fun D => ε (absorb (cbc₂.perPortBound X q) D)]
        cbc₂.perPortBound X q • URF (Evaluation.perPort X X
          (fun _ => cbc₂.bound X * q .eval)) :=
      AdmissibleDistinguishers.substitutesWithin_attach _ secure
    _ = roundURF X := cbc₂_smul_urf X q
    _ ≈[ENNReal.ofReal ((q .eval : ℝ) * (3 * (q .eval : ℝ) - 1) / (2 * Fintype.card X))]
        URF (Messages X q) := roundURF_distance_le X q

/-- **Two-block CBC-MAC at `{0,1}^λ`** [1, §4], the notes' setting: for `F` with keys and blocks
in `{0,1}^λ` and `⊕` the XOR, the collision bound is `q(3q-1)/2^{λ+1}`. The security parameter
`λ` is `secpar`. -/
theorem cbc_mac_2_bits [AdmissibleDistinguishers] {secpar : ℕ}
    (F : Bits secpar → Bits secpar → Bits secpar) (q : Evaluation.Port → ℕ)
    (ε : (Evaluation.perPort (Bits secpar) (Bits secpar)
      (fun _ => cbc₂.bound (Bits secpar) * q .eval)).inputDomain.DistinguisherBehavior → ENNReal)
    (secure : PRF.Secure F ε) :
    PRF.Secure (cbcMAC₂ F) fun D => ε (absorb (cbc₂.perPortBound (Bits secpar) q) D) +
      ENNReal.ofReal ((q .eval : ℝ) * (3 * (q .eval : ℝ) - 1) / 2 ^ (secpar + 1)) := by
  simpa only [card_bits, Nat.cast_pow, Nat.cast_ofNat, ← pow_succ'] using
    cbc_mac_2 F q ε secure

end

end ProofLadders.CBCMAC
