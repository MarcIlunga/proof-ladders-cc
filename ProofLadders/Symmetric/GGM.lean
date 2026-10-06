import ProofLadders.Common.Programs
import ProofLadders.Common.Substitution
import ProofLadders.Common.Symmetric

/-!
# The GGM construction

The third problem of the symmetric ladder [1, §3]: if `G : S → S × S` is a secure
length-doubling PRG on a finite set of seeds `S`, then the GGM construction

$$F(k, X):\ R := k;\ \text{for } i = 1, \dots, n:\ S_0 \,\|\, S_1 := G(R),\ R := S_{X[i]};\
\text{return } R$$

is a secure PRF from `{0,1}^n` to `S`, with keys in `S`. The notes' `{0,1}^λ` is the instance
`S = Bits λ`, with `{0,1}^{2λ}` as `S × S`. An input `X` is the address of a leaf of the binary
tree, a bit string `Bits n`, and bit `i` of `X` is `X (i - 1)`.

The proof is a hybrid argument over the hybrids `L_h` of [1, §3], `h = 0, …, n`, which answer
from a lazy random dictionary on the first `h` bits of `X` and then walk the tree from level `h`;
`L₀` is `prf-real^F` and `L_n` is `prf-rand^F`. The step from `L_h` to `L_{h+1}` is a PRG swap:
its calling program `𝓡 h` takes the two children of each prefix of length `h` from
`prg.samp()`, so `𝓡 h • prg-real^G = L_h` and `𝓡 h • prg-rand = L_{h+1}`, by lazy sampling. The
loss is the sum of the PRG losses at the distinguishers with the `n` calling programs absorbed,
by the hybrid argument.

Style: pure random systems. Every step is an equality of systems or a PRG swap through a
converter; there is no bad event, hence no game.

## Main definitions

* `walk G X h R`: the tree walk from level `h`
* `F G`: the GGM construction
* `𝓡 G h`: the calling program of the swap from `L_h` to `L_{h+1}`
* `prefixOf X h`, `hybrid G h`: the first `h` bits, and the hybrid `L_h` as a sampled function
* `𝓖 G h`: the swap from `L_h` to `L_{h+1}`, without state, on a seed per prefix
* `childrenEquiv h`: a function on the prefixes of length `h + 1` as one on the prefixes of
  length `h` into the values at their two children
* `lazyRel h`: the dictionaries of `𝓡 h` and of `PRG.Lazy` after `𝓖 h` agree at each prefix

## Main results

* `ggm_prf`: the GGM construction is a secure PRF
* `hybrid_step`: the step from `L_h` to `L_{h+1}` through `𝓡 h`
* `walk_step`, `walk_self`, `prefixOf_succ`: the walk and the prefixes one level at a time
* `𝓖_smul_ofFunction`, `𝓖_smul_seeds`, `𝓖_smul_urf`, `hybrid_zero`, `hybrid_last`: the
  hybrids as sampled functions
* `ggm_prf_seeds`, `hybrid_step_seeds`: GGM from the many-seed PRG assumption, and its step
* `𝓡.smul_source`, `𝓡_smul_real`, `𝓡_smul_rand`: `𝓡 h` on a library of fresh samples is the
  lazy random dictionary of the prefixes, on `prg-real^G` and `prg-rand` it is `𝓖 h` on the
  libraries of a sample per prefix
* `𝓡.ofProgram_eq_serial`, `𝓡_eq_𝓖_comp_lazy`: `𝓡 h` is the serial program of `𝓖 h` and
  `PRG.Lazy`, and its converter is `𝓖 h` followed by `PRG.Lazy`

## References

1. The symmetric proof ladder, *Security proofs in the style of The Joy of Cryptography*,
   `proof-ladders/symmetric-ladder`, `Notes/selfcontained.tex`.
-/

namespace ProofLadders.GGM

open Commons Probability SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface CategoryTheory
open scoped SystemAlgebra SystemAlgebra.DSL

variable {S : Type} {n : ℕ}

/-- **The tree walk** from level `h`: starting at `R`, for `i = h + 1, …, n`,
`S₀ ‖ S₁ := G(R)` and `R := S_{X[i]}`. -/
def walk (G : S → S × S) (X : Bits n) (h : ℕ) (R : S) : S :=
  ((List.finRange n).drop h).foldl (fun R i => if X i = 0 then (G R).1 else (G R).2) R

/-- **The GGM construction** [1, §3]: the tree walk from the root, keyed by `k`. -/
def F (G : S → S × S) (k : S) (X : Bits n) : S :=
  walk G X 0 k

/-- The first `h` bits of `X`. -/
def firstBits (X : Bits n) (h : ℕ) : List (ZMod 2) :=
  (List.ofFn X).take h

variable [Fintype S]

-- `𝓡 h`: for `P` the first `h` bits of `X`, if `T[P]` is undefined, `T[P] ← prg.samp()`; then
-- `S₀ ‖ S₁ := T[P]`, `R := S_{X[h+1]}`, and walk the tree from level `h + 1`.
converter 𝓡(n : ℕ) (G : S → S × S) (h : Fin n) : Evaluation (Bits n) S
  inside prg : Evaluation Unit (S × S)
  initialize
    T ← ([] : List (List (ZMod 2) × (S × S)))
  on eval(X : Bits n) → S
    match T.lookup (firstBits X h)
    | some (S₀, S₁) →
      return walk G X (h + 1) (if X h = 0 then S₀ else S₁)
    | none →
      (S₀, S₁) ← prg.eval(())
      T ← T ++ [(firstBits X h, (S₀, S₁))]
      return walk G X (h + 1) (if X h = 0 then S₀ else S₁)

/-! ## Sampled functions

Every hybrid `L_h` of [1, §3] is a sampled function: a uniform function on the prefixes of
length `h`, then the walk from level `h`. The PRG assumption is in its many-seed form,
`PRG.Seeds`, with the prefixes of length `h` as indices. The step from `L_h` to `L_{h+1}` is one
call per query through `𝓖 h`, a converter without state: on `G` with a seed per prefix it is
`L_h`, and on the uniform random function it is `L_{h+1}`, by re-indexing a uniform function on
prefixes into pairs as one on the prefixes one bit longer. The DSL calling program `𝓡 h` is
`𝓖 h` followed by `PRG.Lazy`, which gives each prefix its seed from a fresh sample. -/

/-- The first `h` bits of `X`, as a bit string. -/
def prefixOf (X : Bits n) (h : ℕ) (hh : h ≤ n) : Bits h :=
  fun j => X (Fin.castLE hh j)

-- `𝓖 h`: for `P` the first `h` bits of `X`, `S₀ ‖ S₁ ← prg.query(P)`, `R := S_{X[h+1]}`, and
-- walk the tree from level `h + 1`.
converter 𝓖(n : ℕ) (G : S → S × S) (h : Fin n) : Evaluation (Bits n) S
  inside prg : Evaluation (Bits h.val) (S × S)
  on eval(X : Bits n) → S
    (S₀, S₁) ← prg.eval(prefixOf X h.val h.isLt.le)
    return walk G X (h + 1) (if X h = 0 then S₀ else S₁)

noncomputable section

variable [Nonempty S]

/-- **The hybrid `L_h`** [1, §3] as a sampled function: a uniform `T` on the prefixes of length
`h`, and `X` answered by the walk from level `h` at `T[P]`, for `P` the first `h` bits of `X`. -/
def hybrid (G : S → S × S) (h : Fin (n + 1)) {q : Evaluation.Port → ℕ} :
    Resource (Evaluation.perPort (Bits n) S q) :=
  Resource.sample (Distribution.uniform (Bits h.val → S)) fun T =>
    Resource.ofFunction fun _ X => walk G X h.val (T (prefixOf X h.val (Nat.lt_succ_iff.mp h.isLt)))

omit [Nonempty S] in
/-- **`𝓖 h` on a function** `g` on the prefixes of length `h`. -/
lemma 𝓖_smul_ofFunction (G : S → S × S) (h : Fin n) (q : Evaluation.Port → ℕ)
    (g : Bits h.val → S × S) :
    𝓖.perPort n G h (budget := q) • Resource.ofFunction (fun _ => g) =
      Resource.ofFunction (A := Evaluation.perPort (Bits n) S q) fun _ X =>
        walk G X (h + 1)
          (if X h = 0 then (g (prefixOf X h.val h.isLt.le)).1
            else (g (prefixOf X h.val h.isLt.le)).2) := by
  unfold 𝓖.perPort 𝓖.perPortProgram Interface.Converter.ofPreservingProgram
  refine Interface.ofDDC_ofProgramOn_smul_ofFunction
    (A := Evaluation.perPort (Bits n) S q)
    (B := Evaluation.perPort (Bits h.val) (S × S) (𝓖.insideBudget n G h q))
    none (𝓖.body n G h) (𝓖.bound_spec n G h) _ (fun _ => g) _ fun t o X => ?_
  -- One call per query, answered by `g`.
  cases o
  refine ⟨some (), ?_⟩
  cases t <;> simp [Program.answer, 𝓖.body, callProg, returnProg]

omit [Fintype S] [Nonempty S] in
/-- **One step of the walk**: the walk from level `h` takes the child of `R` at bit `h + 1`, then
walks from level `h + 1`. -/
lemma walk_step (G : S → S × S) (X : Bits n) (h : Fin n) (R : S) :
    walk G X h R = walk G X (h + 1) (if X h = 0 then (G R).1 else (G R).2) := by
  unfold walk
  rw [List.drop_eq_getElem_cons (by simp)]
  simp

omit [Fintype S] [Nonempty S] in
/-- The walk from level `n` is the identity. -/
lemma walk_self (G : S → S × S) (X : Bits n) (R : S) : walk G X n R = R := by
  rw [walk, List.drop_eq_nil_of_le (by simp), List.foldl_nil]

/-- **`𝓖 h` on `G` with a seed per prefix** is `L_h`. -/
lemma 𝓖_smul_seeds (G : S → S × S) (h : Fin n) (q : Evaluation.Port → ℕ) :
    𝓖.perPort n G h (budget := q) • PRG.SeedsReal G (Bits h.val) = hybrid G h.castSucc := by
  unfold PRG.SeedsReal hybrid
  rw [Resource.smul_sample]
  congr 1
  funext s
  refine (𝓖_smul_ofFunction G h q (fun P => G (s P))).trans ?_
  congr 1
  funext _ X
  exact (walk_step G X h _).symm

/-- A bit is `0` or `1`. -/
lemma bit_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := by
  revert b
  decide

lemma bit_one_ne_zero : (1 : ZMod 2) ≠ 0 := by
  decide

/-- **The two children of each prefix**: a function on the prefixes of length `h + 1` is the
function on the prefixes `P` of length `h` into its values at `P ‖ 0` and `P ‖ 1`. -/
def childrenEquiv (h : ℕ) : (Bits (h + 1) → S) ≃ (Bits h → S × S) where
  toFun T P := (T (Fin.snoc P 0), T (Fin.snoc P 1))
  invFun g P := if P (Fin.last h) = 0 then (g (Fin.init P)).1 else (g (Fin.init P)).2
  left_inv T := by
    funext P
    rcases bit_eq_zero_or_one (P (Fin.last h)) with hP | hP <;>
      · simp only [hP, bit_one_ne_zero, if_true, if_false]
        conv_rhs => rw [← Fin.snoc_init_self P, hP]
  right_inv g := by
    funext P
    simp [Fin.init_snoc, Fin.snoc_last]

/-- The first `h + 1` bits are the first `h` bits and bit `h + 1`. -/
lemma prefixOf_succ (X : Bits n) (h : Fin n) :
    prefixOf X (h.val + 1) h.isLt = Fin.snoc (prefixOf X h.val h.isLt.le) (X h) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [prefixOf, Fin.snoc_last]
    exact congrArg X (Fin.ext rfl)
  · simp [prefixOf]

/-- **`𝓖 h` on the uniform random function** is `L_{h+1}`. -/
lemma 𝓖_smul_urf (G : S → S × S) (h : Fin n) (q : Evaluation.Port → ℕ) :
    𝓖.perPort n G h (budget := q) •
        URF (Evaluation.perPort (Bits h.val) (S × S) (𝓖.insideBudget n G h q)) =
      hybrid G h.succ := by
  -- The uniform function on prefixes into pairs, re-indexed as one on the prefixes one bit
  -- longer.
  rw [URF_perPort_eq, Resource.smul_sample,
    Resource.sample_uniform_equiv (childrenEquiv (S := S) h.val)]
  unfold hybrid
  congr 1
  funext T
  refine (𝓖_smul_ofFunction G h q _).trans ?_
  congr 1
  funext _ X
  change _ = walk G X (h.val + 1) (T (prefixOf X (h.val + 1) h.isLt))
  rw [prefixOf_succ]
  rcases bit_eq_zero_or_one (X h) with hX | hX <;> simp [hX, childrenEquiv]

/-- **`L₀` is `prf-real^F`**: the uniform function on the empty prefix is the key. -/
lemma hybrid_zero (G : S → S × S) (q : Evaluation.Port → ℕ) :
    hybrid G 0 (q := q) = PRF.Real (F (n := n) G) := by
  unfold hybrid PRF.Real
  exact Resource.sample_uniform_equiv (K' := Bits (0 : Fin (n + 1)).val → S)
    (Equiv.funUnique (Bits 0) S).symm _

/-- **`L_n` is `prf-rand^F`**: the prefix of length `n` is the whole input. -/
lemma hybrid_last (G : S → S × S) (q : Evaluation.Port → ℕ) :
    hybrid G (Fin.last n) (q := q) = URF (Evaluation.perPort (Bits n) S q) := by
  rw [URF_perPort_eq]
  unfold hybrid
  congr 1
  funext T
  congr 1
  funext _ X
  exact walk_self G X _

/-- **The step from `L_h` to `L_{h+1}`, with many-seed PRG security**: through `𝓖 h`, `G` with a
seed per prefix of length `h` substitutes for the uniform random function on those prefixes. -/
lemma hybrid_step_seeds [AdmissibleDistinguishers] (G : S → S × S) (h : Fin n)
    (q : Evaluation.Port → ℕ)
    (ε : (Evaluation.perPort (Bits h.val) (S × S)
      (𝓖.insideBudget n G h q)).inputDomain.DistinguisherBehavior → ENNReal)
    (secure : PRG.Seeds G (Bits h.val) ε) :
    hybrid G h.castSucc (q := q) ≃[fun D => ε (absorb (𝓖.perPort n G h) D)]
      hybrid G h.succ := by
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    hybrid G h.castSucc = 𝓖.perPort n G h • PRG.SeedsReal G (Bits h.val) :=
      (𝓖_smul_seeds G h q).symm
    _ ≃[ε ∘ absorb (𝓖.perPort n G h)]
        𝓖.perPort n G h • URF (Evaluation.perPort (Bits h.val) (S × S) (𝓖.insideBudget n G h q)) :=
      AdmissibleDistinguishers.substitutesWithin_context _ secure
    _ = hybrid G h.succ := 𝓖_smul_urf G h q

/-- **GGM** [1, §3], with the many-seed PRG assumption: if `G` with a seed per prefix of length
`h` substitutes for the uniform random function within `ε h`, for every `h < n`, then the GGM
construction is a secure PRF within the sum of the losses through the `𝓖 h`. -/
theorem ggm_prf_seeds [AdmissibleDistinguishers] (G : S → S × S) {q : Evaluation.Port → ℕ}
    (ε : (h : Fin n) → (Evaluation.perPort (Bits h.val) (S × S)
      (𝓖.insideBudget n G h q)).inputDomain.DistinguisherBehavior → ENNReal)
    (secure : ∀ h, PRG.Seeds G (Bits h.val) (ε h)) :
    PRF.Secure (F (n := n) G) fun D => ∑ h : Fin n, ε h (absorb (𝓖.perPort n G h) D) := by
  show PRF.Real (F G) ≃[_] URF (Evaluation.perPort (Bits n) S q)
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    PRF.Real (F G) = hybrid G 0 := (hybrid_zero G q).symm
    _ ≃[fun D => ∑ h : Fin n, ε h (absorb (𝓖.perPort n G h) D)] hybrid G (Fin.last n) :=
      ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.hybrid
        _ (fun h => hybrid G h) _
        fun h => hybrid_step_seeds G h q (ε h) (secure h)
    _ = URF (Evaluation.perPort (Bits n) S q) := hybrid_last G q

/-! ## The calling program on fresh samples

The DSL calling program `𝓡 h` keeps a lazy random dictionary of the prefixes of length `h`,
filled from `prg.samp()`; on a library of fresh samples it answers like `𝓖 h` on the library of
a sample per prefix. -/

/-- The first `h` bits as a list are the list of the prefix of length `h`. -/
lemma firstBits_eq_ofFn (X : Bits n) (h : ℕ) (hh : h ≤ n) :
    firstBits X h = List.ofFn (prefixOf X h hh) := by
  apply List.ext_getElem
  · simp [firstBits, hh]
  · intro i h₁ h₂
    simp [firstBits, prefixOf]

omit [Nonempty S] in
/-- `𝓡 h` against a library: a prefix stored in the dictionary is answered from it, a new one
from the library. -/
lemma 𝓡.combine_eq (G : S → S × S) (h : Fin n) {Q : Type}
    (g : Q → (j : (Evaluation Unit (S × S) 0).I) → (Evaluation Unit (S × S) 0).X j →
      Q × (Evaluation Unit (S × S) 0).Y j)
    (ls : Option (List (List (ZMod 2) × (S × S)))) (r : Q) (X : Bits n) :
    (𝓡.body n G h).combine g (𝓡.bound_spec n G h) (ls, r) .eval X =
      match (ls.getD []).lookup (firstBits X h) with
      | some v => ((some (ls.getD []), r), walk G X (h + 1) (if X h = 0 then v.1 else v.2))
      | none => ((some (ls.getD [] ++ [(firstBits X h, (g r .eval ()).2)]), (g r .eval ()).1),
          walk G X (h + 1) (if X h = 0 then (g r .eval ()).2.1 else (g r .eval ()).2.2)) := by
  rcases hl : (ls.getD []).lookup (firstBits X h) with _ | ⟨S₀, S₁⟩
  · rcases hg : g r .eval () with ⟨r', S₀, S₁⟩
    refine Program.combine_eq_of_invoke _ _ (n := 1) ?_
    cases ls <;> simp only [Option.getD] at hl <;>
      simp [Program.invoke, 𝓡.body, callProg, returnProg, hl, hg]
  · refine Program.combine_eq_of_invoke _ _ (n := 0) ?_
    cases ls <;> simp only [Option.getD] at hl <;>
      simp [Program.invoke, 𝓡.body, returnProg, hl]

omit [Nonempty S] in
/-- **`𝓡 h` on a library of fresh samples is the lazy random dictionary of the prefixes**:
attached to a library answering each query with `f` of the next entry of a table of independent
samples of `law`, it is the walk from level `h + 1` at `f` of independent samples of `law` at
every prefix of length `h`. -/
lemma 𝓡.smul_source (G : S → S × S) (h : Fin n) (q : Evaluation.Port → ℕ) {Z : Type}
    [Fintype Z] [DecidableEq Z]
    (law : Distribution.ProbDist Z) (f : Z → S × S) {m : ℕ}
    (g : Option Unit × ((Fin m → Z) × ℕ) → (j : (Evaluation Unit (S × S) 0).I) →
      (Evaluation Unit (S × S) 0).X j →
        (Option Unit × ((Fin m → Z) × ℕ)) × (Evaluation Unit (S × S) 0).Y j)
    (hg : ∀ u t c, g (u, (t, c)) .eval () = ((some (), (t, c + 1)), f (sourceEntry law t c)))
    (hm : q .eval ≤ m) :
    𝓡.perPort n G h (budget := q) •
        Resource.ofAutomaton (Evaluation.perPort Unit (S × S) (𝓡.insideBudget n G h q)) g
          ⟨Distribution.fTransform (fun t => (none, (t, 0)))
            (Distribution.pi fun _ : Fin m => law.1),
            Distribution.fTransform_isProbDist _ (Distribution.pi_isProbDist fun _ => law.2)⟩ =
      Resource.sample (Distribution.pi fun _ : Bits h.val => law.1)
        (fun s => Resource.ofFunction (A := Evaluation.perPort (Bits n) S q)
          fun _ (X : Bits n) => walk G X (h + 1)
            (if X h = 0 then (f (s (prefixOf X h.val h.isLt.le))).1
              else (f (s (prefixOf X h.val h.isLt.le))).2)) := by
  unfold 𝓡.perPort 𝓡.perPortProgram Converter.ofPreservingProgram
  rw [ofDDC_ofProgramOn_smul_ofAutomaton_pi (A := Evaluation.perPort (Bits n) S q)
    (B := Evaluation.perPort Unit (S × S) (𝓡.insideBudget n G h q))
    none (𝓡.body n G h) (𝓡.bound_spec n G h)]
  -- The table holds the dictionary at the lists of the prefixes.
  refine Resource.ofAutomaton_eq_sample_of_lazyDictionary
    (A := Evaluation.perPort (Bits n) S q) (K := Bits h.val)
    _ law _ (fun _ (X : Bits n) => prefixOf X h.val h.isLt.le)
    (fun _ (X : Bits n) z => walk G X (h + 1) (if X h = 0 then (f z).1 else (f z).2))
    (fun t st D => st.2.2 = (t, D.length) ∧ ∀ P, (st.1.getD []).lookup (List.ofFn P) =
      if P ∈ D then some (f (sourceEntry law t (D.idxOf P))) else none)
    (fun t => ⟨rfl, fun P => by simp⟩) ?_ ?_
  · rintro t hist ⟨⟨⟩, X⟩ ⟨ls, u, t', c⟩ D hd ⟨hpos, hT⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpos
    rw [𝓡.combine_eq, hg, firstBits_eq_ofFn X h.val h.isLt.le]
    by_cases hp : prefixOf X h.val h.isLt.le ∈ D
    · rw [hT _, if_pos hp]
      simp only [lazyDictionary, if_pos hp]
      exact ⟨trivial, trivial, hT⟩
    · rw [hT _, if_neg hp]
      simp only [lazyDictionary, if_neg hp, List.idxOf_append_of_notMem hp, List.idxOf_cons_self,
        add_zero, List.length_append, List.length_singleton]
      exact ⟨trivial, trivial, lookup_append_of_dictionary List.ofFn List.ofFn_injective
        (f := fun r => f (sourceEntry law _ r)) hT hp⟩
  · intro hist hd
    exact (List.toFinset_card_le _).trans ((List.length_map _).trans_le
      ((evaluation_length_le (Or.inr hd)).trans hm))

/-- **`𝓡 h` on `prg-real^G` is `𝓖 h` on `G` with a seed per prefix**: the seed of each prefix is
the fresh seed of its first query. -/
lemma 𝓡_smul_real (G : S → S × S) (h : Fin n) (q : Evaluation.Port → ℕ) :
    𝓡.perPort n G h (budget := q) • PRG.Real.perPort G =
      𝓖.perPort n G h (budget := q) • PRG.SeedsReal G (Bits h.val) := by
  classical
  unfold PRG.Real.perPort Converter.ofProgram PRG.Real.randomness Resource.source
  rw [ofDDC_ofProgramOn_smul_ofAutomaton_pi
    (A := Evaluation.perPort Unit (S × S) (𝓡.insideBudget n G h q))
    (B := Interface.source S (PRG.Real.bound G * ∑ i, 𝓡.insideBudget n G h q i))
    none (PRG.Real.body G) (PRG.Real.bound_spec G),
    𝓡.smul_source G h q (PRG.Real.law1 G) G _ (PRG.Real.combine_eq G)
      (by simp [PRG.Real.bound, 𝓡.insideBudget]),
    PRG.SeedsReal, Resource.smul_sample]
  refine (Resource.sample_congr_law (P := Distribution.pi fun _ => (PRG.Real.law1 G).1)
    (P' := Distribution.uniform (Bits h.val → S)) Distribution.pi_uniform _).trans ?_
  congr 1
  funext s
  exact (𝓖_smul_ofFunction G h q (fun P => G (s P))).symm

/-- **`𝓡 h` on `prg-rand` is `𝓖 h` on the uniform random function**: the pair of each prefix is
the fresh sample of its first query. -/
lemma 𝓡_smul_rand (G : S → S × S) (h : Fin n) (q : Evaluation.Port → ℕ) :
    𝓡.perPort n G h (budget := q) • PRG.Rand.perPort (S × S) =
      𝓖.perPort n G h (budget := q) •
        URF (Evaluation.perPort (Bits h.val) (S × S) (𝓖.insideBudget n G h q)) := by
  classical
  unfold PRG.Rand.perPort Converter.ofProgram PRG.Rand.randomness Resource.source
  rw [ofDDC_ofProgramOn_smul_ofAutomaton_pi
    (A := Evaluation.perPort Unit (S × S) (𝓡.insideBudget n G h q))
    (B := Interface.source (S × S) (PRG.Rand.bound (S × S) * ∑ i, 𝓡.insideBudget n G h q i))
    none (PRG.Rand.body _) (PRG.Rand.bound_spec _),
    𝓡.smul_source G h q (PRG.Rand.law1 _) id _ PRG.Rand.combine_eq
      (by simp [PRG.Rand.bound, 𝓡.insideBudget]),
    URF_perPort_eq, Resource.smul_sample]
  refine (Resource.sample_congr_law (P := Distribution.pi fun _ => (PRG.Rand.law1 (S × S)).1)
    (P' := Distribution.uniform (Bits h.val → S × S)) Distribution.pi_uniform _).trans ?_
  congr 1
  funext g
  exact (𝓖_smul_ofFunction G h q g).symm

/-- **The step from `L_h` to `L_{h+1}`** [1, §3]: through the calling program `𝓡 h`,
`prg-real^G` substitutes for `prg-rand`. -/
theorem hybrid_step [AdmissibleDistinguishers] (G : S → S × S) (h : Fin n)
    (q : Evaluation.Port → ℕ)
    (ε : (Evaluation.perPort Unit (S × S)
      (𝓡.insideBudget n G h q)).inputDomain.DistinguisherBehavior → ENNReal)
    (secure : PRG.Samples G ε) :
    hybrid G h.castSucc (q := q) ≃[fun D => ε (absorb (𝓡.perPort n G h) D)]
      hybrid G h.succ := by
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    hybrid G h.castSucc = 𝓖.perPort n G h • PRG.SeedsReal G (Bits h.val) :=
      (𝓖_smul_seeds G h q).symm
    _ = 𝓡.perPort n G h • PRG.Real.perPort G := (𝓡_smul_real G h q).symm
    _ ≃[ε ∘ absorb (𝓡.perPort n G h)] 𝓡.perPort n G h • PRG.Rand.perPort (S × S) :=
      AdmissibleDistinguishers.substitutesWithin_context _ secure
    _ = 𝓖.perPort n G h • URF (Evaluation.perPort (Bits h.val) (S × S)
        (𝓖.insideBudget n G h q)) := 𝓡_smul_rand G h q
    _ = hybrid G h.succ := 𝓖_smul_urf G h q

/-- The dictionaries of `𝓡 h` and of `PRG.Lazy` after `𝓖 h` agree at each prefix. -/
def lazyRel (h : Fin n) (tR : Option (List (List (ZMod 2) × (S × S))))
    (tc : Option Unit × Option (List (Bits h.val × (S × S)))) : Prop :=
  ∀ P : Bits h.val, (tR.getD []).lookup (List.ofFn P) = (tc.2.getD []).lookup P

/-- **`𝓡 h` is the serial program of `𝓖 h` and `PRG.Lazy`**: both keep a dictionary of the
prefixes queried, at the list of the prefix and at the prefix, and answer alike. -/
lemma 𝓡.ofProgram_eq_serial (G : S → S × S) (h : Fin n) :
    DDC.ofProgram none (𝓡.body n G h) =
      DDC.ofProgram (none, none) ((𝓖.body n G h).serial (PRG.Lazy.body (Bits h.val) (S × S))
        (𝓖.bound n G h) fun _ => Classical.arbitrary S) := by
  refine DDC.ofProgram_eq_of_bisim (lazyRel h) (fun _ => rfl) fun tR tc hrel o X hist hc => ?_
  cases o
  have hkey : (tc.2.getD []).lookup (prefixOf X h.val h.isLt.le) =
      (tR.getD []).lookup (firstBits X h) := by
    rw [firstBits_eq_ofFn X h.val h.isLt.le, hrel]
  obtain ⟨u₁, ls⟩ := tc
  rcases hl : (tR.getD []).lookup (firstBits X h) with _ | ⟨S₀, S₁⟩
  · -- A new prefix: one query, answered by `PRG.Lazy`'s query.
    have hbody : 𝓡.body n G h tR .eval X = callProg .eval () (fun value =>
        returnProg (some (tR.getD [] ++ [(firstBits X h, value)]),
          walk G X (h + 1) (if X h = 0 then value.1 else value.2))) := by
      rcases tR with _ | T <;> simp only [Option.getD] at hl ⊢ <;> simp only [𝓡.body, hl]
    change Program.ExchangesOf (𝓡.body n G h tR .eval X) hist at hc
    rw [hbody] at hc ⊢
    rcases hist with _ | ⟨e, hist⟩
    · refine ⟨fun q _ => ?_, fun t₁ v hv => by simp [callProg] at hv⟩
      rw [hl] at hkey
      rcases u₁ with _ | ⟨⟨⟩⟩ <;> rcases ls with _ | TL <;> simp only [Option.getD] at hkey <;>
        simp [Program.serial, Program.serialLoop, 𝓖.body, PRG.Lazy.body, callProg, hkey]
    · obtain ⟨y, rfl, he, hc'⟩ := DSL.exchangesOf_callProg hc
      -- After the reply the body returns: no further exchange.
      rcases hist with _ | ⟨e', hist'⟩
      swap
      · exact absurd (hc' 0 (by simp)).1 (by simp [returnProg])
      rw [he]
      refine ⟨fun q hq => by simp [returnProg] at hq, fun t₁ v hv => ?_⟩
      simp only [returnProg, Sum.inl.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      refine ⟨(some (), some (ls.getD [] ++ [(prefixOf X h.val h.isLt.le, y)])), ?_, fun P => ?_⟩
      · rw [hl] at hkey
        rcases u₁ with _ | ⟨⟨⟩⟩ <;> rcases ls with _ | TL <;> simp only [Option.getD] at hkey ⊢ <;>
          simp [Program.serial, Program.serialLoop, 𝓖.body, PRG.Lazy.body, callProg, returnProg,
            hkey]
      · have hP := hrel P
        simp only [Option.getD_some] at hP ⊢
        rw [List.lookup_append, List.lookup_append, hP, firstBits_eq_ofFn X h.val h.isLt.le]
        by_cases hPX : P = prefixOf X h.val h.isLt.le
        · simp [hPX]
        · have h₁ : (List.ofFn P == List.ofFn (prefixOf X h.val h.isLt.le)) = false :=
            beq_false_of_ne (List.ofFn_injective.ne hPX)
          have h₂ : (P == prefixOf X h.val h.isLt.le) = false := beq_false_of_ne hPX
          simp only [List.lookup_cons, List.lookup_nil, h₁, h₂]
  · -- A stored prefix: answered from the dictionary.
    rcases tR with _ | T
    · simp at hl
    have hbody : 𝓡.body n G h (some T) .eval X =
        returnProg (some T, walk G X (h + 1) (if X h = 0 then S₀ else S₁)) := by
      simp only [Option.getD] at hl
      simp only [𝓡.body, hl]
    change Program.ExchangesOf (𝓡.body n G h (some T) .eval X) hist at hc
    rw [hbody] at hc ⊢
    rcases hist with _ | ⟨e, hist⟩
    swap
    · exact absurd (hc 0 (by simp)).1 (by simp [returnProg])
    refine ⟨fun q hq => by simp [returnProg] at hq, fun t₁ v hv => ?_⟩
    simp only [returnProg, Sum.inl.injEq, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    rw [hl] at hkey
    refine ⟨(some (), some (ls.getD [])), ?_, fun P => by simpa using hrel P⟩
    rcases u₁ with _ | ⟨⟨⟩⟩ <;> rcases ls with _ | TL <;> simp only [Option.getD] at hkey ⊢
    · simp at hkey
    · simp [Program.serial, Program.serialLoop, 𝓖.body, PRG.Lazy.body, callProg, returnProg,
        hkey]
    · simp at hkey
    · simp [Program.serial, Program.serialLoop, 𝓖.body, PRG.Lazy.body, callProg, returnProg,
        hkey]

/-- **The DSL calling program is `𝓖 h` and the lazy seeds**: `𝓡 h`, which draws the two
children of each new prefix from `prg.samp()`, is `𝓖 h` followed by `PRG.Lazy`. -/
lemma 𝓡_eq_𝓖_comp_lazy (G : S → S × S) (h : Fin n) (q : Evaluation.Port → ℕ) :
    𝓡.perPort n G h (budget := q) =
      𝓖.perPort n G h ≫ PRG.Lazy.perPort (Bits h.val) (S × S) := by
  unfold 𝓡.perPort 𝓡.perPortProgram 𝓖.perPort 𝓖.perPortProgram PRG.Lazy.perPort
    PRG.Lazy.perPortProgram Converter.ofPreservingProgram
  refine (Interface.ofDDC_ofProgramOn_comp (A := Evaluation.perPort (Bits n) S q)
    (B := Evaluation.perPort (Bits h.val) (S × S) (𝓖.insideBudget n G h q))
    (C := Evaluation.perPort Unit (S × S)
      (PRG.Lazy.insideBudget (Bits h.val) (S × S) (𝓖.insideBudget n G h q)))
    none (𝓖.body n G h) (𝓖.bound_spec n G h) _ none
    (PRG.Lazy.body (Bits h.val) (S × S)) _ (fun _ => Classical.arbitrary S) _
    fun xs ys hr => ?_).symm
  rw [← 𝓡.ofProgram_eq_serial]
  exact hr.mono fun h y hy => ((filterDom_mem_iff _ _ h y).mp hy).2

/-- **GGM** [1, §3]: if `G` is a secure PRG within `ε`, then the GGM construction is a secure PRF
within the sum of the losses of the `n` hybrid steps. -/
theorem ggm_prf [AdmissibleDistinguishers] (G : S → S × S) {q : Evaluation.Port → ℕ}
    (ε : (Evaluation.perPort Unit (S × S) q).inputDomain.DistinguisherBehavior → ENNReal)
    (secure : PRG.Samples G ε) :
    PRF.Secure (F (n := n) G) fun D => ∑ h : Fin n, ε (absorb (𝓡.perPort n G h) D) := by
  show PRF.Real (F G) ≃[_] URF (Evaluation.perPort (Bits n) S q)
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    PRF.Real (F G) = hybrid G 0 := (hybrid_zero G q).symm
    _ ≃[fun D => ∑ h : Fin n, ε (absorb (𝓡.perPort n G h) D)] hybrid G (Fin.last n) :=
      ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.hybrid
        _ (fun h => hybrid G h) _
        fun h => hybrid_step G h q ε secure
    _ = URF (Evaluation.perPort (Bits n) S q) := hybrid_last G q

end

end ProofLadders.GGM
