import ProofLadders.Common.Symmetric
import ProofLadders.Common.Memoryless
import ConstructiveCryptography.Tactics.Substitution

/-!
# PRG length extension

The first problem of the symmetric ladder [1, §1]: if `G : S → S × S` is a secure
length-doubling PRG on a finite set of seeds `S`, then

$$H(s) = A \,\|\, C \,\|\, D, \qquad A \,\|\, B := G(s), \quad C \,\|\, D := G(B),$$

is a secure PRG from `S` to `S × S × S`. The notes' `{0,1}^λ` is the instance `S = Bits λ`, with
`{0,1}^{2λ}` and `{0,1}^{3λ}` as `S × S` and `S × S × S`.

The proof is two 3-hop maneuvers [1, §1.1], one per call of `G`: each factors one call out into
`prg-real^G`, swaps it for `prg-rand`, and inlines the result. The calling programs of the two
swaps are the converters `𝓡₁` and `𝓡₂`, and the loss is the PRG loss at the distinguishers
with them absorbed.

Style: pure random systems. Both swaps are substitutions through a converter and the other hops
are equalities of systems; there is no bad event, hence no game. Every system of the proof is
memoryless [2, Definition 3.1]: it replies to each query with a fresh sample of one law. So each
equality of systems is an equality of these laws, on `S`, `S × S` and `S × S × S`.

```
 system                 law of one reply (U = 𝒰[S])
 prg-real^H             H_* U
 = 𝓡₁ • prg-real^G      (a, G b)_* (G_* U)       equal laws: H = (a, G b) ∘ G
 ≃ 𝓡₁ • prg-rand        (a, G b)_* U²
 = 𝓡₂ • prg-real^G      U ⊗ G_* U                equal laws: (a, b) ↦ (a, G b) is id × G
 ≃ 𝓡₂ • prg-rand        U ⊗ U²
 = prg-rand^H           U³                       equal laws: a product of uniforms
```

## Main definitions

* `H G`: the length-extended generator
* `𝓡₁ G`, `𝓡₂ S`: the calling programs of the two swaps
* `Indexed.𝓡₁ m G`, `Indexed.𝓡₂ S m`: the swaps on the libraries indexed by the query number

## Main results

* `prgReal_eq_source`, `prgRand_eq_source`: `prg-real^G` and `prg-rand` are memoryless sources
* `𝓡₁_smul_source`, `𝓡₂_smul_source`: `𝓡₁` and `𝓡₂` on memoryless sources
* `prgReal_H_eq`, `𝓡₁_smul_prgRand`, `𝓡₂_smul_prgRand`: the equalities of the two maneuvers
* `prg_length_extension`: `H` is a secure PRG
* `Indexed.𝓡₁_smul_ofFunction`, `Indexed.𝓡₂_smul_ofFunction`, `Indexed.𝓡₁_smul_seeds`,
  `Indexed.𝓡₁_smul_urf`, `Indexed.𝓡₂_smul_urf`: the swaps on sampled functions
* `Indexed.prg_length_extension_seeds`: `H` is a secure many-seed PRG

## References

1. The symmetric proof ladder, *Security proofs in the style of The Joy of Cryptography*,
   `proof-ladders/symmetric-ladder`, `Notes/selfcontained.tex`.
2. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

namespace ProofLadders.PRGLengthExtension

open Commons Probability SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface
open scoped SystemAlgebra SystemAlgebra.DSL

/-- **The length-extended generator** `H(s) = A ‖ C ‖ D`, for `A ‖ B := G(s)` and
`C ‖ D := G(B)`. -/
def H {S : Type} (G : S → S × S) (seed : S) : S × S × S :=
  let (A, B) := G seed
  let (C, D) := G B
  (A, C, D)

variable {S : Type} [Fintype S]

-- `𝓡₁`: `A ‖ B ← prg.samp()`, `C ‖ D := G(B)`, return `A ‖ C ‖ D`.
converter 𝓡₁(G : S → S × S) : Evaluation Unit (S × S × S)
  inside prg : Evaluation Unit (S × S)
  on eval(_input : Unit) → S × S × S
    (A, B) ← prg.eval(())
    return (A, G B)

-- `𝓡₂`: `A ← S`, `C ‖ D ← prg.samp()`, return `A ‖ C ‖ D`.
converter 𝓡₂(S : Type) [Fintype S] [Nonempty S] : Evaluation Unit (S × S × S)
  inside prg : Evaluation Unit (S × S)
  on eval(_input : Unit) → S × S × S
    A ←$ 𝒰[S]
    CD ← prg.eval(())
    return (A, CD)

noncomputable section

open Probability.Distribution

/-! ### The systems of the proof are memoryless sources

Every system of the proof replies to each `eval(())` with a fresh sample, independent of the
history: it is the memoryless source of the law `ν` of one reply, the DSL system
`MemorylessSource ν` (`Common/Memoryless`). The calling programs map memoryless sources to
memoryless sources:

```
  system                 law of one reply to eval(())
  ─────────────────────  ──────────────────────────────────────────
  prg-real^G             G s                  for s ← 𝒰[S]
  prg-rand  (on R)       y                    for y ← 𝒰[R]
  𝓡₁ • source of ν       (a, G b)             for (a, b) ← ν
  𝓡₂ • source of ν       (a, c, d)            for a ← 𝒰[S], (c, d) ← ν
```

Each lemma below compares random systems (`.1`): two systems on the same interface are equal
when their random systems are equal (`Subtype.ext`), and both random systems are computed as
memoryless systems. -/

variable {q : Evaluation.Port → ℕ}

/-- **`prg-real^G` is the memoryless source of `G(s)` for a uniform seed `s`.** -/
lemma prgReal_eq_source [Nonempty S] {R : Type} [Fintype R] (G : S → R) :
    PRG.Real.perPort G (budget := q) = MemorylessSource.perPort R (ProbDist.map G 𝒰[S]) := by
  -- Equal systems: compare their random systems.
  apply Subtype.ext
  -- `prg-real^G` is its program attached to its source of seeds:
  --
  --   eval(()) ──► program ── randomness(()) ──► source, seeds s ← 𝒰[S]
  --            ◄── eval ⇒ G s
  --
  -- The source is memoryless (fresh samples of 𝒰[S]), so by the composition law `prg-real^G`
  -- is memoryless with the law of one invocation of the program.
  have real : (PRG.Real.perPort G (budget := q)).1 =
      RandomSystem.memoryless _ (RandomSystem.portLaw fun _ _ => ProbDist.map G 𝒰[S]) := by
    refine Converter.ofProgram_smul_memoryless (FreshSampling.source _ _)
      (ProbStep.memoryless_fresh _) none _ _ _ ?_
    -- The law of one invocation: draw `s ← 𝒰[S]`, reply `G s`. Two cases, by the
    -- initialization state (`none` before the first call, `some ()` after); same body in both.
    rintro (_ | ⟨⟩) ⟨⟩ ⟨⟩
    · simp [Program.replyLaw, PRG.Real.body, PRG.Real.law1, callProg, returnProg,
        ProbDist.map, bindK_single_comp]
    · simp [Program.replyLaw, PRG.Real.body, PRG.Real.law1, callProg, returnProg,
        ProbDist.map, bindK_single_comp]
  -- The memoryless source of `G_* 𝒰[S]` is the same memoryless system.
  rw [real, MemorylessSource.memoryless_eq]

/-- **`prg-rand` is the memoryless source of uniform samples.** -/
lemma prgRand_eq_source (R : Type) [Fintype R] [Nonempty R] :
    PRG.Rand.perPort R (budget := q) = MemorylessSource.perPort R 𝒰[R] := by
  apply Subtype.ext
  -- As for `prg-real`, with one invocation:  eval(()) ──► draw y ← 𝒰[R] ──► reply y.
  have rand : (PRG.Rand.perPort R (budget := q)).1 =
      RandomSystem.memoryless _ (RandomSystem.portLaw fun _ _ => 𝒰[R]) := by
    refine Converter.ofProgram_smul_memoryless (FreshSampling.source _ _)
      (ProbStep.memoryless_fresh _) none _ _ _ ?_
    rintro (_ | ⟨⟩) ⟨⟩ ⟨⟩
    · simp [Program.replyLaw, PRG.Rand.body, PRG.Rand.law1, callProg, returnProg,
        bindK_single_one]
    · simp [Program.replyLaw, PRG.Rand.body, PRG.Rand.law1, callProg, returnProg,
        bindK_single_one]
  rw [rand, MemorylessSource.memoryless_eq]

/-- **`𝓡₁` on the memoryless source** of `A ‖ B` is the memoryless source of `A ‖ G(B)`. -/
lemma 𝓡₁_smul_source (G : S → S × S) (ν : ProbDist (S × S)) :
    𝓡₁.perPort G (budget := q) • MemorylessSource.perPort (S × S) ν =
      MemorylessSource.perPort (S × S × S) (ProbDist.map (fun AB => (AB.1, G AB.2)) ν) := by
  apply Subtype.ext
  -- One invocation of 𝓡₁ against the source of ν:
  --
  --   eval(()) ──► 𝓡₁ ── prg.eval(()) ──► source of ν replies (a, b) ← ν
  --            ◄── eval ⇒ (a, G b)
  --
  -- so `𝓡₁ • source` is memoryless with the law (a, G b)_* ν.
  have attached : (𝓡₁.perPort G (budget := q) •
      MemorylessSource.perPort (S × S) ν (budget := 𝓡₁.insideBudget G q)).1 =
      RandomSystem.memoryless _
        (RandomSystem.portLaw fun _ _ => ProbDist.map (fun AB => (AB.1, G AB.2)) ν) := by
    -- `𝓡₁.perPort` is the converter of a port-preserving program; unfolding it lets the
    -- composition law see the program (its proof-only arguments are not found otherwise).
    unfold 𝓡₁.perPort 𝓡₁.perPortProgram
    -- The source of ν is presented as fresh sampling, with a memoryless step of law ν.
    refine Converter.ofPreservingProgram_smul_memoryless (MemorylessSource.freshSampling ν _)
      (MemorylessSource.step_memoryless ν _) none _ _ _ _ _ _ _ ?_
    -- The law of one invocation of 𝓡₁'s body: one call, answered `(a, b) ← ν`, reply
    -- `(a, G b)`; the same in both initialization states.
    rintro (_ | ⟨⟩) ⟨⟩ ⟨⟩
    · simp [Program.replyLaw, 𝓡₁.body, callProg, returnProg, ProbDist.map, bindK_single_comp]
    · simp [Program.replyLaw, 𝓡₁.body, callProg, returnProg, ProbDist.map, bindK_single_comp]
  -- The memoryless source of (a, G b)_* ν is the same memoryless system.
  rw [attached, MemorylessSource.memoryless_eq]

/-- **`𝓡₂` on the memoryless source** of `C ‖ D` is the memoryless source of `A ‖ C ‖ D` for a
uniform `A`. -/
lemma 𝓡₂_smul_source [Nonempty S] (ν : ProbDist (S × S)) :
    𝓡₂.perPort S (budget := q) • MemorylessSource.perPort (S × S) ν =
      MemorylessSource.perPort (S × S × S) (prodProbDist 𝒰[S] ν) := by
  apply Subtype.ext
  -- One invocation of 𝓡₂ against the source of ν, with its own source of `A`'s beside:
  --
  --   eval(()) ──► 𝓡₂ ── randomness(()) ──► own source replies a ← 𝒰[S]
  --                   ── prg.eval(())   ──► source of ν replies (c, d) ← ν
  --            ◄── eval ⇒ (a, c, d)
  --
  -- so `𝓡₂ • source` is memoryless with the law 𝒰[S] ⊗ ν.
  have attached : (𝓡₂.perPort S (budget := q) •
      MemorylessSource.perPort (S × S) ν (budget := 𝓡₂.insideBudget S q)).1 =
      RandomSystem.memoryless _ (RandomSystem.portLaw fun _ _ => prodProbDist 𝒰[S] ν) := by
    -- `𝓡₂.perPort` is its program composed with its own source placed beside the inside
    -- interface (`≫ rightContext`); unfold to expose both.
    unfold 𝓡₂.perPort 𝓡₂.perPortProgram 𝓡₂.randomness
    -- The composition law for a program with a source beside it: the source of ν (memoryless,
    -- law ν) and 𝓡₂'s own source (law 𝒰[S]) side by side.
    refine Converter.ofPreservingProgram_comp_rightContext_smul_memoryless
      (MemorylessSource.freshSampling ν _) (MemorylessSource.step_memoryless ν _) (𝓡₂.law1 S) _
      none _ _ _ _ _ _ _ ?_
    -- The law of one invocation of 𝓡₂'s body: `a` from its own source, `(c, d)` from the
    -- source of ν, reply `(a, c, d)`; the product of the two laws, in both initialization states.
    rintro (_ | ⟨⟩) ⟨⟩ ⟨⟩
    · simp [Program.replyLaw, 𝓡₂.body, 𝓡₂.law1, ProbStep.parallelLaw, callProg, returnProg,
        prod_eq_bindK, bindK_single_comp]
    · simp [Program.replyLaw, 𝓡₂.body, 𝓡₂.law1, ProbStep.parallelLaw, callProg, returnProg,
        prod_eq_bindK, bindK_single_comp]
  -- The memoryless source of 𝒰[S] ⊗ ν is the same memoryless system.
  rw [attached, MemorylessSource.memoryless_eq]

/-! ### The hops

Each hop rewrites both sides into memoryless sources and compares the laws of one reply. -/

variable [Nonempty S]

/-- `(A, G(B))` for a uniform `A ‖ B` is a uniform `A` beside `G(s)` for a uniform `s`. -/
lemma map_uniform_eq_prod (G : S → S × S) :
    ProbDist.map (fun AB => (AB.1, G AB.2)) 𝒰[S × S] = prodProbDist 𝒰[S] (ProbDist.map G 𝒰[S]) := by
  -- Compare the underlying distributions.
  apply Subtype.ext
  -- `(a, b) ↦ (a, G b)` is the product map `id × G`.
  change fTransform (Prod.map id G) (Distribution.uniform (S × S)) = _
  -- 𝒰[S × S] is 𝒰[S] ⊗ 𝒰[S] ...
  rw [← prod_uniform]
  -- ... a product map acts factor by factor ...
  rw [fTransform_prod]
  -- ... and `id` leaves 𝒰[S] unchanged.
  rw [fTransform_id]
  rfl

/-- **The first hop**, "factor out": `prg-real^H` is `𝓡₁` on `prg-real^G`. -/
lemma prgReal_H_eq (G : S → S × S) (q : Evaluation.Port → ℕ) :
    PRG.Real.perPort (H G) (budget := q) =
      𝓡₁.perPort G • PRG.Real.perPort G (budget := 𝓡₁.insideBudget G q) := by
  -- Left:   prg-real^H        = source of H_* U
  -- Right:  𝓡₁ • prg-real^G   = 𝓡₁ • source of G_* U  =  source of (a, G b)_* (G_* U)
  -- Equal laws, because H = (a, G b) ∘ G.
  rw [prgReal_eq_source (H G), prgReal_eq_source G, 𝓡₁_smul_source]
  -- Pushing forward twice is pushing forward along the composite ...
  rw [ProbDist.map_map]
  -- ... and `(a, G b) ∘ G` is `H`: `H s = (A, G B)` for `(A, B) := G s`, by definition.
  rfl

/-- **The middle hop**, "inline, split, factor out": `𝓡₁` on `prg-rand` is `𝓡₂` on
`prg-real^G`, a uniform `A` beside `G(s)` for a uniform `s` either way. -/
lemma 𝓡₁_smul_prgRand (G : S → S × S) (q : Evaluation.Port → ℕ) :
    𝓡₁.perPort G (budget := q) • PRG.Rand.perPort (S × S) (budget := 𝓡₁.insideBudget G q) =
      𝓡₂.perPort S • PRG.Real.perPort G (budget := 𝓡₂.insideBudget S q) := by
  -- Left:   𝓡₁ • prg-rand    = 𝓡₁ • source of 𝒰[S × S]  =  source of (a, G b)_* 𝒰[S × S]
  rw [prgRand_eq_source, 𝓡₁_smul_source]
  -- Right:  𝓡₂ • prg-real^G  = 𝓡₂ • source of G_* 𝒰[S]   =  source of 𝒰[S] ⊗ G_* 𝒰[S]
  rw [prgReal_eq_source, 𝓡₂_smul_source]
  -- Equal laws: (a, G b) for a uniform pair is a uniform `a` beside `G` of a uniform seed.
  rw [map_uniform_eq_prod]

/-- **The last hop**, "inline, concatenate": `𝓡₂` on `prg-rand` is `prg-rand`, a uniform `A`
beside a uniform `C ‖ D`. -/
lemma 𝓡₂_smul_prgRand (q : Evaluation.Port → ℕ) :
    𝓡₂.perPort S (budget := q) • PRG.Rand.perPort (S × S) (budget := 𝓡₂.insideBudget S q) =
      PRG.Rand.perPort (S × S × S) (budget := q) := by
  -- Left:   𝓡₂ • prg-rand  = 𝓡₂ • source of 𝒰[S × S]  =  source of 𝒰[S] ⊗ 𝒰[S × S]
  rw [prgRand_eq_source (S × S), 𝓡₂_smul_source]
  -- Right:  prg-rand on S × S × S = source of 𝒰[S × S × S]
  rw [prgRand_eq_source (S × S × S)]
  -- Equal laws: a product of uniform laws is the uniform law on the product.
  rw [show prodProbDist 𝒰[S] 𝒰[S × S] = 𝒰[S × S × S] from Subtype.ext prod_uniform]

/-- **PRG length extension** [1, §1]: if `G` is a secure PRG within `ε`, then `H` is a secure
PRG within the losses of the two swaps. -/
theorem prg_length_extension [AdmissibleDistinguishers] (G : S → S × S) {q : Evaluation.Port → ℕ}
    (ε : (Evaluation.perPort Unit (S × S) q).inputDomain.DistinguisherBehavior → ENNReal)
    (secure : PRG.Samples G ε) :
    PRG.Samples (H G) fun D => ε (absorb (𝓡₁.perPort G) D) + ε (absorb (𝓡₂.perPort S) D) := by
  -- The notes' hybrids, as systems (the distinguisher D on the left):
  --
  --   D ─ prg-real^H                                start
  --   D ─ 𝓡₁ ─ prg-real^G      =                    factor out            prgReal_H_eq
  --   D ─ 𝓡₁ ─ prg-rand        ≃[ε(D ∘ 𝓡₁)]         swap: PRG security of G
  --   D ─ 𝓡₂ ─ prg-real^G      =                    inline, split, factor  𝓡₁_smul_prgRand
  --   D ─ 𝓡₂ ─ prg-rand        ≃[ε(D ∘ 𝓡₂)]         swap: PRG security of G
  --   D ─ prg-rand^H           =                    inline, concatenate   𝓡₂_smul_prgRand
  --
  -- `cc_calc` chains `=` and `≃[·]` steps for the admitted distinguishers; the losses add up.
  -- Its first line names the distinguishing advantage, and how it is bounded by the distance.
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    -- factor out the first call of G into prg-real^G, with the calling program 𝓡₁
    PRG.Real.perPort (H G) = 𝓡₁.perPort G • PRG.Real.perPort G := prgReal_H_eq G q
    -- swap prg-real^G for prg-rand inside the context 𝓡₁: the PRG assumption at the
    -- distinguisher D ∘ 𝓡₁ (𝓡₁ absorbed into D)
    _ ≃[fun D => ε (absorb (𝓡₁.perPort G) D)]
        𝓡₁.perPort G • PRG.Rand.perPort (S × S) :=
      AdmissibleDistinguishers.substitutesWithin_attach _ secure
    -- inline prg-rand, split the uniform pair, and factor out the second call of G with 𝓡₂
    _ = 𝓡₂.perPort S • PRG.Real.perPort G := 𝓡₁_smul_prgRand G q
    -- swap again, inside the context 𝓡₂: the PRG assumption at D ∘ 𝓡₂
    _ ≃[fun D => ε (absorb (𝓡₂.perPort S) D)]
        𝓡₂.perPort S • PRG.Rand.perPort (S × S) :=
      AdmissibleDistinguishers.substitutesWithin_attach _ secure
    -- inline prg-rand and concatenate: a uniform A beside a uniform C ‖ D is uniform
    _ = PRG.Rand.perPort (S × S × S) := 𝓡₂_smul_prgRand q

end

/-! ## Sampled functions

`prg-real` gives a fresh sample per query; indexed by the query number, it is `G` on a seed per
index, sampled once (`PRG.SeedsReal`, with `prgReal_eq_index`). In that form the two swaps are
converters on sampled functions: `Indexed.𝓡₁` calls once per index and post-processes, and
`Indexed.𝓡₂` samples its `A`'s once and calls once per index. The middle hop is an equality of
output laws, `(A, G(B))` for uniform `A, B` against `A` and `G(s)` for uniform `A, s`. -/

namespace Indexed

-- `𝓡₁`: on the index `k`, `A ‖ B ← prg(k)` and return `A ‖ G(B)`.
converter 𝓡₁(m : ℕ) (G : S → S × S) : Evaluation (Fin m) (S × S × S)
  inside prg : Evaluation (Fin m) (S × S)
  on eval(k : Fin m) → S × S × S
    (A, B) ← prg.eval(k)
    return (A, G B)

-- `𝓡₂`: a uniform `A_k` for every index, sampled once; on `k`, return `A_k ‖ prg(k)`.
converter 𝓡₂(S : Type) [Fintype S] [Nonempty S] (m : ℕ) : Evaluation (Fin m) (S × S × S)
  inside prg : Evaluation (Fin m) (S × S)
  initialize
    As ←$ 𝒰[Fin m → S]
  on eval(k : Fin m) → S × S × S
    CD ← prg.eval(k)
    return (As k, CD)

noncomputable section

variable [Nonempty S] (m : ℕ)

omit [Nonempty S] in
/-- **`𝓡₁` on a function** `g`: `((g k)₁, G((g k)₂))`. -/
lemma 𝓡₁_smul_ofFunction (G : S → S × S) (q : Evaluation.Port → ℕ) (g : Fin m → S × S) :
    𝓡₁.perPort m G (budget := q) • Resource.ofFunction (fun _ => g) =
      Resource.ofFunction (A := Evaluation.perPort (Fin m) (S × S × S) q)
        fun _ k => ((g k).1, G (g k).2) := by
  unfold 𝓡₁.perPort 𝓡₁.perPortProgram Interface.Converter.ofPreservingProgram
  refine Interface.ofDDC_ofProgramOn_smul_ofFunction
    (A := Evaluation.perPort (Fin m) (S × S × S) q)
    (B := Evaluation.perPort (Fin m) (S × S) (𝓡₁.insideBudget m G q))
    none (𝓡₁.body m G) (𝓡₁.bound_spec m G) _ (fun _ => g) _ fun t o k => ?_
  -- One call per index, answered by `g`.
  cases o
  refine ⟨some (), ?_⟩
  cases t <;> simp [Program.answer, 𝓡₁.body, callProg, returnProg]

/-- `𝓡₂` against `g` and a source table: the first invocation reads the `A`'s from the table. -/
lemma 𝓡₂_combine_first (g : Fin m → S × S) {k : ℕ} (t : Fin k → (Fin m → S)) (c : ℕ)
    (i : Fin m) :
    (𝓡₂.body S m).combine (parallelStep (fun (_ : Unit) _ x => ((), g x))
        (sourceStep (q := k) (𝓡₂.law1 S m))) (𝓡₂.bound_spec S m)
        (none, ((), (t, c))) .eval i =
      ((some (sourceEntry (𝓡₂.law1 S m) t c), ((), (t, c + 1))),
        (sourceEntry (𝓡₂.law1 S m) t c i, g i)) :=
  Program.combine_eq_of_invoke _ _ (n := 2) (by
    simp [Program.invoke, 𝓡₂.body, callProg, returnProg, parallelStep, sourceStep,
      sourceEntry])

/-- `𝓡₂` against `g` once the `A`'s are stored. -/
lemma 𝓡₂_combine_later (g : Fin m → S × S) {k : ℕ}
    (As : Fin m → S) (r : Unit × ((Fin k → (Fin m → S)) × ℕ)) (i : Fin m) :
    (𝓡₂.body S m).combine (parallelStep (fun (_ : Unit) _ x => ((), g x))
        (sourceStep (q := k) (𝓡₂.law1 S m))) (𝓡₂.bound_spec S m)
        (some As, r) .eval i = ((some As, r), (As i, g i)) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, 𝓡₂.body, callProg, returnProg, parallelStep])

/-- **`𝓡₂` on a function** `g`: uniform `A_k`, sampled once, and `(A_k, g k)`. -/
lemma 𝓡₂_smul_ofFunction (q : Evaluation.Port → ℕ) (g : Fin m → S × S) :
    𝓡₂.perPort S m (budget := q) • Resource.ofFunction (fun _ => g) =
      Resource.sample (Distribution.uniform (Fin m → S)) fun As =>
        Resource.ofFunction (A := Evaluation.perPort (Fin m) (S × S × S) q)
          fun _ k => (As k, g k) := by
  -- The initialization sample is the converter's only randomness: the source is read once.
  rw [𝓡₂.perPort, 𝓡₂.randomness, 𝓡₂.perPortProgram]
  refine Converter.ofPreservingProgram_source_smul_ofFunction
    (A := Evaluation.perPort (Fin m) (S × S × S) q)
    (B := Evaluation.perPort (Fin m) (S × S) (𝓡₂.insideBudget S m q))
    (Z := Fin m → S) (k := 𝓡₂.bound S m * ∑ i, q i)
    none (𝓡₂.body S m) (𝓡₂.bound_spec S m) (𝓡₂.portMap S m) _ q _ _
    (𝓡₂.law1 S m) (fun _ => g) (fun As _ k => (As k, g k))
    (fun t c => automatonSystem_of_stored _ (fun As _ k => (As k, g k)) ((), (t, c))
      (sourceEntry (𝓡₂.law1 S m) t c)
      (fun j k => ⟨_, 𝓡₂_combine_first m g t c k⟩)
      (fun r j k => ⟨_, 𝓡₂_combine_later m g _ r k⟩))
    fun _ hd => Nat.mul_pos (by norm_num [𝓡₂.bound]) (bound_pos_of_domain hd)

/-- **The first swap on `G` with a seed per index** is `H` with a seed per index. -/
lemma 𝓡₁_smul_seeds (G : S → S × S) (q : Evaluation.Port → ℕ) :
    𝓡₁.perPort m G (budget := q) • PRG.SeedsReal G (Fin m) =
      PRG.SeedsReal (H G) (Fin m) := by
  unfold PRG.SeedsReal
  rw [Resource.smul_sample]
  congr 1
  funext s
  exact 𝓡₁_smul_ofFunction m G q (fun k => G (s k))

/-- **The first swap on the uniform random function** is the second swap on `G` with a seed per
index: `(A_k, G(B_k))` for uniform `A`'s and `B`'s. -/
lemma 𝓡₁_smul_urf (G : S → S × S) (q : Evaluation.Port → ℕ) :
    𝓡₁.perPort m G (budget := q) •
        URF (Evaluation.perPort (Fin m) (S × S) (𝓡₁.insideBudget m G q)) =
      𝓡₂.perPort S m • PRG.SeedsReal G (Fin m) := by
  -- The uniform function into pairs is the pair of uniform functions of the seeds and the `A`'s.
  let e : (Fin m → S) × (Fin m → S) ≃ (Fin m → S × S) :=
    (Equiv.prodComm _ _).trans (Equiv.arrowProdEquivProdArrow _ _ _).symm
  rw [URF_perPort_eq, Resource.smul_sample, Resource.sample_uniform_equiv e]
  unfold PRG.SeedsReal
  rw [Resource.smul_sample]
  have h₂ : ∀ s : Fin m → S, 𝓡₂.perPort S m (budget := q) •
      Resource.ofFunction (fun _ k => G (s k)) =
        Resource.sample (Distribution.uniform (Fin m → S)) fun As =>
          Resource.ofFunction (A := Evaluation.perPort (Fin m) (S × S × S) q)
            fun _ k => (As k, G (s k)) :=
    fun s => 𝓡₂_smul_ofFunction m q (fun k => G (s k))
  simp only [𝓡₁_smul_ofFunction, h₂]
  rw [Resource.sample_sample]
  congr 1
  exact Distribution.prod_uniform.symm

/-- **The second swap on the uniform random function** is the uniform random function into
`S × S × S`. -/
lemma 𝓡₂_smul_urf (q : Evaluation.Port → ℕ) :
    𝓡₂.perPort S m (budget := q) •
        URF (Evaluation.perPort (Fin m) (S × S) (𝓡₂.insideBudget S m q)) =
      URF (Evaluation.perPort (Fin m) (S × S × S) q) := by
  -- The uniform function into triples is the pair of its components.
  let e : (Fin m → S × S) × (Fin m → S) ≃ (Fin m → S × S × S) :=
    (Equiv.prodComm _ _).trans (Equiv.arrowProdEquivProdArrow _ _ _).symm
  rw [URF_perPort_eq (Fin m) (S × S), URF_perPort_eq (Fin m) (S × S × S), Resource.smul_sample,
    Resource.sample_uniform_equiv e]
  simp only [𝓡₂_smul_ofFunction]
  rw [Resource.sample_sample]
  congr 1
  exact Distribution.prod_uniform

/-- **PRG length extension** [1, §1], with a seed per index: if `G` with a seed per index
substitutes for the uniform random function within `ε`, so does `H`, within the losses of the
two swaps. -/
theorem prg_length_extension_seeds [AdmissibleDistinguishers] (G : S → S × S)
    {q : Evaluation.Port → ℕ}
    (ε : (Evaluation.perPort (Fin m) (S × S)
      (𝓡₁.insideBudget m G q)).inputDomain.DistinguisherBehavior → ENNReal)
    (secure : PRG.Seeds G (Fin m) ε) :
    PRG.Seeds (H G) (Fin m) (q := q) fun D =>
      ε (absorb (𝓡₁.perPort m G) D) + ε (absorb (𝓡₂.perPort S m) D) := by
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    PRG.SeedsReal (H G) (Fin m) = 𝓡₁.perPort m G • PRG.SeedsReal G (Fin m) :=
      (𝓡₁_smul_seeds m G q).symm
    _ ≃[fun D => ε (absorb (𝓡₁.perPort m G) D)]
        𝓡₁.perPort m G • URF (Evaluation.perPort (Fin m) (S × S) (𝓡₁.insideBudget m G q)) :=
      AdmissibleDistinguishers.substitutesWithin_attach _ secure
    _ = 𝓡₂.perPort S m • PRG.SeedsReal G (Fin m) := 𝓡₁_smul_urf m G q
    _ ≃[fun D => ε (absorb (𝓡₂.perPort S m) D)]
        𝓡₂.perPort S m • URF (Evaluation.perPort (Fin m) (S × S) (𝓡₂.insideBudget S m q)) :=
      AdmissibleDistinguishers.substitutesWithin_attach _ secure
    _ = URF (Evaluation.perPort (Fin m) (S × S × S) q) := 𝓡₂_smul_urf m q

end

end Indexed

end ProofLadders.PRGLengthExtension
