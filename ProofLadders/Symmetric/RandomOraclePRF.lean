import ProofLadders.Common.Symmetric
import ProofLadders.Common.Functional
import ConstructiveCryptography.Tactics.Substitution

/-!
# The random-oracle PRF

The sixth problem of the symmetric ladder [1, §6]: `F(k, x) = RO(k ‖ x)` is a secure PRF when
`RO` is a random oracle, that is, `prf-real+ro ≈ prf-rand+ro`. Both libraries also give the
adversary the random oracle itself, at the port `ro`. Keys are in a finite set `K`, inputs in a
finite set `X` and outputs in a finite set `Y`; the oracle is queried on pairs `k ‖ x` in
`K × X`. The notes' keys in `{0,1}^λ`, inputs in `{0,1}^m` and outputs in `{0,1}^n` are the
instance `K = Bits λ`, `X = Bits m`, `Y = Bits n` (`ro_prf_bits`, `ro_prf_sampled_bits`);
there the oracle is queried on strings `k ‖ x` of length `λ + m`, and queries of other lengths
are answered independently of the PRF.

The libraries are sampled functions: `prf-real+ro` samples the key and the oracle once, and
`prf-rand+ro` the lazy random dictionary and the oracle. They differ only when the adversary
queries the oracle on `k ‖ x` for the key `k`, the partitioning argument of [1, §6]. As a game
with that hidden condition, `prf-real+ro` is equivalent to `prf-rand+ro`
(`roPRF_game_equiv`); the key is uniform and independent of the queries, so blind winning is at
most `q_ro / |K|` (`roPRFGame_blind_bound`), which bounds the distance (`ro_prf`). At
`K = Bits λ` the bound is `q_ro / 2^λ`.

Style: games, since the step is a bad event of a sampled function; the claim itself is the
distance of the two libraries as random systems.

## Main definitions

* `PRFRO K X Y`: the interface of the PRF and the random oracle
* `PRFRealRO K X Y`, `PRFRandRO K X Y`: the libraries `prf-real+ro` and `prf-rand+ro`
* `KeyQuery`, `roPRFGame K X Y`: an oracle query at the key, and the game
* `𝓚 K X Y k`, `𝓚.perPortBound K X Y k`: the oracle seen through the key `k`, and its typing at
  per-port budgets

## Main results

* `roPRF_game_equiv`, `roPRFGame_visible`, `roPRFGame_blind_bound`: the game
* `ro_prf`: `prf-real+ro` is within `q_ro / |K|` of `prf-rand+ro`
* `𝓚_smul_ofFunction`, `prfRealRO_eq`, `prfRandRO_eq`, `ro_prf_sampled`: the libraries as
  converters on the uniform random function, and the theorem in that form
* `ro_prf_bits`, `ro_prf_sampled_bits`: both at `{0,1}^λ`, within `q_ro / 2^λ`

## References

1. The symmetric proof ladder, *Security proofs in the style of The Joy of Cryptography*,
   `proof-ladders/symmetric-ladder`, `Notes/selfcontained.tex`.
-/

namespace ProofLadders.RandomOraclePRF

open Commons Probability SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface
open scoped SystemAlgebra SystemAlgebra.DSL

interface PRFRO(K X Y : Type) [Fintype K] [Fintype X] [Fintype Y]
  query(x : X) → Y
  ro(a : K × X) → Y

noncomputable section

variable (K X Y : Type) [Fintype K] [Fintype X] [Fintype Y]

/-- The interface of the two libraries, at the budget `q` per port. -/
abbrev Queries (q : PRFRO.Port → ℕ) : Interface :=
  PRFRO.perPort K X Y q

variable {K X Y}

/-- An oracle query `ro(k ‖ x)` at the key `k`. -/
def KeyQuery (k : K) {q : PRFRO.Port → ℕ} : (Σ i, (Queries K X Y q).X i) → Prop
  | ⟨.query, _⟩ => False
  | ⟨.ro, a⟩ => a.1 = k

lemma keyQuery_monotone (k : K) {q : PRFRO.Port → ℕ}
    {xs xs' : List (Σ i, (Queries K X Y q).X i)} (hp : xs <+: xs') :
    (∃ x ∈ xs, KeyQuery k x) → ∃ x ∈ xs', KeyQuery k x :=
  fun ⟨x, hx, hk⟩ => ⟨x, hp.subset hx, hk⟩

variable (K X Y) [Nonempty K] [DecidableEq K] [DecidableEq X] [Nonempty Y]

/-- **`prf-real+ro`** [1, §6]: a uniform key `k` and a uniform oracle `RO`; `query(x)` returns
`RO(k ‖ x)` and `ro(a)` returns `RO(a)`. -/
def PRFRealRO {q : PRFRO.Port → ℕ} : Resource (Queries K X Y q) :=
  Resource.sample (Distribution.uniform (K × (K × X → Y)))
    fun kRO => Resource.ofFunction fun
      | .query => fun x => kRO.2 (kRO.1, x)
      | .ro => fun a => kRO.2 a

/-- **`prf-rand+ro`** [1, §6]: a lazy random dictionary `T` and a uniform oracle `RO`;
`query(x)` returns `T[x]` and `ro(a)` returns `RO(a)`. -/
def PRFRandRO {q : PRFRO.Port → ℕ} : Resource (Queries K X Y q) :=
  Resource.sample (Distribution.uniform ((X → Y) × (K × X → Y)))
    fun TRO => Resource.ofFunction fun
      | .query => fun x => TRO.1 x
      | .ro => fun a => TRO.2 a

/-- The answers of `prf-real+ro` for the key and the oracle `kRO`. -/
def realAnswer {q : PRFRO.Port → ℕ} (kRO : K × (K × X → Y)) :
    (Σ i, (Queries K X Y q).X i) → Σ i, (Queries K X Y q).Y i
  | ⟨.query, x⟩ => ⟨.query, kRO.2 (kRO.1, x)⟩
  | ⟨.ro, a⟩ => ⟨.ro, kRO.2 a⟩

/-- **The game** of the partitioning argument: `prf-real+ro`, with the hidden condition that the
adversary queried the oracle at the key. -/
def roPRFGame (q : PRFRO.Port → ℕ) :=
  PDG.ofFunction (Queries K X Y q).domain (Queries K X Y q).nonempty_prefix
    (Queries K X Y q).bound (Queries K X Y q).length_le
    (Distribution.uniform (K × (K × X → Y)))
    (realAnswer K X Y)
    (fun kRO => ⟨fun xs => ∃ x ∈ xs, KeyQuery kRO.1 x,
      fun {_ _} hp => keyQuery_monotone kRO.1 hp⟩)

/-- Until an oracle query at the key, `prf-real+ro` answers `query` and `ro` at disjoint points of
a uniform oracle, which is the law of `prf-rand+ro`. -/
lemma roPRF_game_equiv (q : PRFRO.Port → ℕ) :
    roPRFGame K X Y q |≡ PRFRandRO K X Y (q := q) := by
  classical
  -- The ideal answers: `T` at queries and `RO` at oracle queries.
  let tagged : ((X → Y) × (K × X → Y)) →
      (Σ i, (Queries K X Y q).X i) → Σ i, (Queries K X Y q).Y i :=
    fun TRO x => ⟨x.1, (fun
      | .query => TRO.1
      | .ro => TRO.2 : ∀ i, (Queries K X Y q).X i → (Queries K X Y q).Y i) x.1 x.2⟩
  have ideal : (PRFRandRO K X Y (q := q)).1 = PDS.behavior (PDS.ofFunction
      (Queries K X Y q).domain (Queries K X Y q).nonempty_prefix
      (Queries K X Y q).bound (Queries K X Y q).length_le id
      (Distribution.fTransform tagged (Distribution.uniform _)))
      (Distribution.fTransform_isProbDist _ (Distribution.fTransform_isProbDist _
        Distribution.uniform_isProbDist)) := by
    apply RandomSystem.ext
    intro h
    rw [PRFRandRO, Resource.sample_ofFunction_mass]
    change _ = behaviorMass _ _ _
    simp only [behaviorMass, PDS.ofFunction, Distribution.mass_fTransform]
    rfl
  rw [ideal]
  refine PDG.ofFunction_gameEquivalent _ _ _ _ _ _ _ _
    (Distribution.fTransform_isProbDist _ Distribution.uniform_isProbDist) fun xs answers => ?_
  -- The answers carry the queried label; their values are those of the oracle at the key's
  -- points, and of `(T, RO)` at disjoint points.
  let value : (Σ i, (Queries K X Y q).Y i) → Y := fun
    | ⟨.query, y⟩ => y
    | ⟨.ro, y⟩ => y
  have sigma_ext : ∀ z w : Σ i, (Queries K X Y q).Y i,
      z = w ↔ z.1 = w.1 ∧ value z = value w := by
    rintro ⟨i, y⟩ ⟨j, y'⟩
    cases i <;> cases j <;> simp [value]
  let keyPoint : K → (Σ i, (Queries K X Y q).X i) → K × X :=
    fun k => fun
    | ⟨.query, x⟩ => (k, x)
    | ⟨.ro, a⟩ => a
  let idealPoint : (Σ i, (Queries K X Y q).X i) → X ⊕ (K × X) := fun
    | ⟨.query, x⟩ => .inl x
    | ⟨.ro, a⟩ => .inr a
  let Labels := ∀ x ∈ xs, (answers x).1 = x.1
  have real : ∀ kRO, (∀ x ∈ xs, realAnswer K X Y kRO x = answers x) ↔
      Labels ∧ ∀ x ∈ xs, kRO.2 (keyPoint kRO.1 x) = value (answers x) := by
    intro kRO
    have point : ∀ x, realAnswer K X Y kRO x = answers x ↔
        (answers x).1 = x.1 ∧ kRO.2 (keyPoint kRO.1 x) = value (answers x) := by
      rintro ⟨_ | _, x⟩ <;> rw [sigma_ext] <;>
        exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩
    simp only [point]
    exact ⟨fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩,
      fun h x hx => ⟨h.1 x hx, h.2 x hx⟩⟩
  have ideal' : ∀ TRO, (∀ x ∈ xs, tagged TRO x = answers x) ↔
      Labels ∧ ∀ x ∈ xs, Sum.elim TRO.1 TRO.2 (idealPoint x) = value (answers x) := by
    intro TRO
    have point : ∀ x, tagged TRO x = answers x ↔
        (answers x).1 = x.1 ∧ Sum.elim TRO.1 TRO.2 (idealPoint x) = value (answers x) := by
      rintro ⟨_ | _, x⟩ <;> rw [sigma_ext] <;>
        exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩
    simp only [point]
    exact ⟨fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩,
      fun h x hx => ⟨h.1 x hx, h.2 x hx⟩⟩
  dsimp only
  rw [Distribution.mass_fTransform]
  simp only [real, ideal']
  by_cases hl : Labels
  · simp only [hl, true_and]
    have hQ : (Distribution.uniform ((X → Y) × (K × X → Y))).mass
        (fun TRO => ∀ x ∈ xs, Sum.elim TRO.1 TRO.2 (idealPoint x) = value (answers x)) =
          (1 / (Fintype.card Y : ℝ)) ^ xs.toFinset.card := by
      rw [← Distribution.fTransform_equiv_uniform (Equiv.sumArrowEquivProdArrow _ _ _),
        Distribution.mass_fTransform]
      have elim : ∀ f : X ⊕ (K × X) → Y,
          Sum.elim ((Equiv.sumArrowEquivProdArrow _ _ _) f).1
            ((Equiv.sumArrowEquivProdArrow _ _ _) f).2 = f :=
        fun f => Sum.elim_comp_inl_inr f
      simp only [elim]
      refine Counting.uniform_mass_apply_list_eq xs idealPoint ?_ _
      rintro ⟨_ | _, x⟩ - ⟨_ | _, x'⟩ - h <;> simp_all [idealPoint]
    rw [hQ, ← Distribution.prod_uniform,
      Distribution.mass_prod_fst (R := fun k => ∃ x ∈ xs, KeyQuery k x),
      Distribution.weight_uniform, mul_one]
    refine (Distribution.mass_prod_eq_sum _ _ (fun (k : K)
      (RO : K × X → Y) => (∀ x ∈ xs, RO (keyPoint k x) = value (answers x)) ∧
        ¬ ∃ x ∈ xs, KeyQuery k x)).trans ?_
    have fresh : ∀ k : K,
        (Distribution.uniform (K × X → Y)).mass
          (fun RO => (∀ x ∈ xs, RO (keyPoint k x) = value (answers x)) ∧
            ¬ ∃ x ∈ xs, KeyQuery k x) =
        if ¬ ∃ x ∈ xs, KeyQuery k x then (1 / (Fintype.card Y : ℝ)) ^ xs.toFinset.card
        else 0 := by
      intro k
      by_cases hk : ∃ x ∈ xs, KeyQuery k x
      · rw [if_neg (not_not.mpr hk)]
        exact Distribution.mass_eq_zero_of_forall_not _ fun _ h => h.2 hk
      · rw [if_pos hk, ← Counting.uniform_mass_apply_list_eq xs (keyPoint k) ?_ _]
        · exact Distribution.mass_congr _ fun RO => and_iff_left hk
        -- Without an oracle query at the key, the key's points are distinct from the oracle
        -- queries.
        rintro ⟨_ | _, x⟩ hx ⟨_ | _, x'⟩ hx' h
        · simp_all [keyPoint]
        · exact (hk ⟨_, List.mem_toFinset.mp hx',
            show x'.1 = k by rw [← show (k, x) = x' from h]⟩).elim
        · exact (hk ⟨_, List.mem_toFinset.mp hx,
            show x.1 = k by rw [show x = (k, x') from h]⟩).elim
        · simp_all [keyPoint]
    simp only [fresh, mul_ite, mul_zero]
    have hbad := Distribution.mass_add_compl (Distribution.uniform K)
      (fun k => ∃ x ∈ xs, KeyQuery k x)
    rw [Distribution.weight_uniform] at hbad
    rw [show (1 : ℝ) - (Distribution.uniform K).mass (fun k => ∃ x ∈ xs, KeyQuery k x)
        = (Distribution.uniform K).mass (fun k => ¬ ∃ x ∈ xs, KeyQuery k x) by
      linarith]
    rw [Distribution.mass, Finsupp.sum_mul]
    exact Finsupp.sum_congr fun k _ => by split_ifs <;> ring
  · simp only [hl, false_and]
    rw [Distribution.mass_eq_zero_of_forall_not _ fun _ h => h,
      Distribution.mass_eq_zero_of_forall_not _ fun _ h => h, mul_zero]

/-- Blind winning is an oracle query at a uniform key among at most `q_ro` fixed queries. -/
lemma roPRFGame_blind_bound (q : PRFRO.Port → ℕ) :
    ν((roPRFGame K X Y q).blind (Queries K X Y q).nonempty_prefix) ≤
      (q .ro : ℝ) / Fintype.card K := by
  apply PDG.ofFunction_blind_le (by positivity)
  intro xs hxs
  have hro : (SystemAlgebra.restrict PRFRO.Port.ro xs).length ≤ q .ro := by
    rcases hxs with rfl | hxs
    · exact Nat.zero_le _
    · exact hxs.2 _
  -- An oracle query at the key is one of the oracle queries at the uniform key.
  have queried : ∀ (k : K) (xs : List (Σ i, (Queries K X Y q).X i)),
      (∃ x ∈ xs, KeyQuery k x) →
        ∃ a ∈ (SystemAlgebra.restrict PRFRO.Port.ro xs).toFinset, a.1 = k := by
    intro k xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rintro ⟨y, hy, hk⟩
      obtain ⟨i, a⟩ := x
      rcases List.mem_cons.mp hy with rfl | hy
      · cases i
        · exact hk.elim
        · exact ⟨a, by simp, hk⟩
      · obtain ⟨a', ha', ha'k⟩ := ih ⟨y, hy, hk⟩
        refine ⟨a', ?_, ha'k⟩
        cases i <;> simp_all
  change (Distribution.uniform (K × (K × X → Y))).mass
    (fun kRO => ∃ x ∈ xs, KeyQuery kRO.1 x) ≤ _
  rw [← Distribution.prod_uniform, Distribution.mass_prod_fst (R := fun k =>
    ∃ x ∈ xs, KeyQuery k x), Distribution.weight_uniform, mul_one]
  refine (Distribution.mass_mono Distribution.uniform_nonNeg (queried · xs)).trans
    ((Distribution.mass_exists_le Distribution.uniform_nonNeg _ _).trans ?_)
  have single : ∀ a : K × X,
      (Distribution.uniform K).mass (fun k => a.1 = k) = 1 / Fintype.card K := by
    intro a
    rw [Distribution.mass_congr _ fun k => eq_comm, Distribution.mass_singleton,
      Distribution.uniform_apply]
  simp only [single, Finset.sum_const, nsmul_eq_mul]
  rw [mul_one_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact_mod_cast (List.toFinset_card_le _).trans hro

/-- **The visible systems of the game are `prf-real+ro`.** -/
lemma roPRFGame_visible (q : PRFRO.Port → ℕ) :
    (PRFRealRO K X Y (q := q)).1 = PDS.behavior (roPRFGame K X Y q).underlying
      (PDG.underlying_probability
        (PDG.ofFunction_isProbDist _ _ _ _ Distribution.uniform_isProbDist _ _)) := by
  apply RandomSystem.ext
  intro h
  rw [PRFRealRO, Resource.sample_ofFunction_mass]
  change _ = behaviorMass _ _ _
  rw [roPRFGame, PDG.ofFunction_underlying]
  simp only [behaviorMass, PDS.ofFunction, Distribution.mass_fTransform]
  refine Distribution.mass_congr _ fun kRO => ?_
  have answers : realAnswer K X Y kRO = fun x => ⟨x.1, (fun
      | .query => fun x => kRO.2 (kRO.1, x)
      | .ro => fun a => kRO.2 a : ∀ i, (Queries K X Y q).X i → (Queries K X Y q).Y i)
        x.1 x.2⟩ := by
    funext ⟨i, x⟩
    cases i <;> rfl
  rw [answers]

/-- **The random-oracle PRF** [1, §6]: `prf-real+ro` is within `q_ro / |K|` of `prf-rand+ro`.
The game step bounds the distance by blind winning, which is at most `q_ro / |K|`. -/
theorem ro_prf (q : PRFRO.Port → ℕ) :
    Δ (PRFRealRO K X Y (q := q)) (PRFRandRO K X Y (q := q)) ≤
      ENNReal.ofReal ((q .ro : ℝ) / Fintype.card K) :=
  calc Δ (PRFRealRO K X Y (q := q)) (PRFRandRO K X Y (q := q))
      ≤ ENNReal.ofReal ν((roPRFGame K X Y q).blind (Queries K X Y q).nonempty_prefix) :=
        (roPRF_game_equiv K X Y q).game_dist_le
          (PDG.ofFunction_isProbDist _ _ _ _ Distribution.uniform_isProbDist _ _)
          (roPRFGame_visible K X Y q)
    _ ≤ ENNReal.ofReal ((q .ro : ℝ) / Fintype.card K) :=
        ENNReal.ofReal_le_ofReal (roPRFGame_blind_bound K X Y q)

/-- **The random-oracle PRF at `{0,1}^λ`** [1, §6], the notes' statement: with keys in
`{0,1}^λ`, inputs in `{0,1}^m` and outputs in `{0,1}^n`, `prf-real+ro` is within `q_ro / 2^λ`
of `prf-rand+ro`. The security parameter `λ` is `secpar`. -/
theorem ro_prf_bits (secpar m n : ℕ) (q : PRFRO.Port → ℕ) :
    Δ (PRFRealRO (Bits secpar) (Bits m) (Bits n) (q := q))
        (PRFRandRO (Bits secpar) (Bits m) (Bits n) (q := q)) ≤
      ENNReal.ofReal ((q .ro : ℝ) / 2 ^ secpar) := by
  simpa only [card_bits, Nat.cast_pow, Nat.cast_ofNat] using
    ro_prf (Bits secpar) (Bits m) (Bits n) q

/-! ## Sampled functions

`prf-rand+ro` is the uniform random function on its two ports. `prf-real+ro` is the oracle seen
through a uniform key: for each key `k`, the converter `𝓚 k`, without state, answers `query(x)`
with `oracle(k ‖ x)` and `ro(a)` with `oracle(a)`, one call per query to one oracle;
`𝓚.perPortBound` types it at per-port budgets. -/

end

-- `𝓚 k`: answer `query(x)` with `oracle(k ‖ x)` and `ro(a)` with `oracle(a)`.
converter 𝓚(K X Y : Type) [Fintype K] [Fintype X] [Fintype Y] (k : K) : PRFRO K X Y
  inside oracle : Evaluation (K × X) Y
  on query(x : X) → Y
    y ← oracle.eval((k, x))
    return y
  on ro(a : K × X) → Y
    y ← oracle.eval(a)
    return y

noncomputable section

variable (K X Y : Type) [Fintype K] [Fintype X] [Fintype Y]

/-- **`𝓚 k` at per-port budgets**: every query makes at most `𝓚.bound = 1` call to the
oracle. -/
def 𝓚.perPortBound (k : K) (q : PRFRO.Port → ℕ) :
    Queries K X Y q ⟶ Evaluation.perPort (K × X) Y (fun _ => 𝓚.bound K X Y k * ∑ i, q i) :=
  Interface.Converter.ofProgramPerPort none (𝓚.body K X Y k) (𝓚.bound_spec K X Y k) q
    (∑ i, q i) le_rfl

/-- **`𝓚 k` on an oracle** `RO`: `query(x) = RO(k ‖ x)` and `ro(a) = RO(a)`. -/
lemma 𝓚_smul_ofFunction (k : K) (q : PRFRO.Port → ℕ) (RO : K × X → Y) :
    𝓚.perPortBound K X Y k q • Resource.ofFunction (fun _ => RO) =
      Resource.ofFunction (A := Queries K X Y q) fun
        | .query => fun x => RO (k, x)
        | .ro => fun a => RO a := by
  unfold 𝓚.perPortBound Interface.Converter.ofProgramPerPort Interface.Converter.ofProgram
  refine Interface.ofDDC_ofProgramOn_smul_ofFunction (A := Queries K X Y q)
    (B := Evaluation.perPort (K × X) Y (fun _ => 𝓚.bound K X Y k * ∑ i, q i))
    none (𝓚.body K X Y k) (𝓚.bound_spec K X Y k) _ (fun _ => RO) _ fun t o x => ?_
  -- One call per query, answered by `RO`.
  refine ⟨some (), ?_⟩
  cases o <;> cases t <;> simp [Program.answer, 𝓚.body, callProg, returnProg]

variable [Nonempty K] [DecidableEq K] [DecidableEq X] [Nonempty Y]

/-- **`prf-real+ro` is the oracle seen through a uniform key.** -/
lemma prfRealRO_eq (q : PRFRO.Port → ℕ) :
    PRFRealRO K X Y (q := q) =
      Resource.sample (Distribution.uniform K) fun k =>
        𝓚.perPortBound K X Y k q •
          URF (Evaluation.perPort (K × X) Y (fun _ => 𝓚.bound K X Y k * ∑ i, q i)) := by
  simp only [URF_perPort_eq, Resource.smul_sample, 𝓚_smul_ofFunction]
  rw [Resource.sample_sample]
  unfold PRFRealRO
  congr 1
  exact Distribution.prod_uniform.symm

/-- Both ports answer in `Y`. -/
instance (q : PRFRO.Port → ℕ) : ∀ i, Nonempty ((Queries K X Y q).Y i)
  | .query => ‹Nonempty Y›
  | .ro => ‹Nonempty Y›

omit [Nonempty K] in
/-- **`prf-rand+ro` is the uniform random function** on its two ports. -/
lemma prfRandRO_eq (q : PRFRO.Port → ℕ) :
    PRFRandRO K X Y (q := q) = URF (Queries K X Y q) := by
  -- The functions of the interface are the pairs `(T, RO)`.
  let e : ((X → Y) × (K × X → Y)) ≃
      (∀ i, (Queries K X Y q).X i → (Queries K X Y q).Y i) :=
    ⟨fun TRO => fun | .query => TRO.1 | .ro => TRO.2, fun F => (F .query, F .ro),
      fun _ => rfl, fun F => funext fun i => by cases i <;> rfl⟩
  rw [URF_eq_sample _ e]
  rfl

/-- **The random-oracle PRF** [1, §6], on sampled functions: the oracle seen through a uniform
key is within `q_ro / |K|` of the uniform random function on the two ports. -/
theorem ro_prf_sampled (q : PRFRO.Port → ℕ) :
    Δ (Resource.sample (Distribution.uniform K) fun k =>
        𝓚.perPortBound K X Y k q •
          URF (Evaluation.perPort (K × X) Y (fun _ => 𝓚.bound K X Y k * ∑ i, q i)))
        (URF (Queries K X Y q)) ≤
      ENNReal.ofReal ((q .ro : ℝ) / Fintype.card K) := by
  cc_calc statistical
    (Resource.sample (Distribution.uniform K) fun k =>
        𝓚.perPortBound K X Y k q •
          URF (Evaluation.perPort (K × X) Y (fun _ => 𝓚.bound K X Y k * ∑ i, q i))) =
        PRFRealRO K X Y (q := q) :=
      (prfRealRO_eq K X Y q).symm
    _ ≈[ENNReal.ofReal ((q .ro : ℝ) / Fintype.card K)] PRFRandRO K X Y (q := q) :=
      ro_prf K X Y q
    _ = URF (Queries K X Y q) := prfRandRO_eq K X Y q

/-- **The random-oracle PRF at `{0,1}^λ`** [1, §6], on sampled functions: with keys in
`{0,1}^λ`, inputs in `{0,1}^m` and outputs in `{0,1}^n`, the oracle seen through a uniform key
is within `q_ro / 2^λ` of the uniform random function. The security parameter `λ` is
`secpar`. -/
theorem ro_prf_sampled_bits (secpar m n : ℕ) (q : PRFRO.Port → ℕ) :
    Δ (Resource.sample (Distribution.uniform (Bits secpar)) fun k =>
        𝓚.perPortBound (Bits secpar) (Bits m) (Bits n) k q •
          URF (Evaluation.perPort (Bits secpar × Bits m) (Bits n)
            (fun _ => 𝓚.bound (Bits secpar) (Bits m) (Bits n) k * ∑ i, q i)))
        (URF (Queries (Bits secpar) (Bits m) (Bits n) q)) ≤
      ENNReal.ofReal ((q .ro : ℝ) / 2 ^ secpar) := by
  simpa only [card_bits, Nat.cast_pow, Nat.cast_ofNat] using
    ro_prf_sampled (Bits secpar) (Bits m) (Bits n) q

end

end ProofLadders.RandomOraclePRF
