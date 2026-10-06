import Commons.Definitions.Signature
import ProofLadders.Common.RSA
import ProofLadders.Common.Substitution
import ProofLadders.Common.Symmetric
import ProofLadders.Common.Programs
import ProofLadders.Common.Mixtures
import ProofLadders.Common.UntilBad

/-!
# RSA-PSS

The RSA-PSS problem of the ladder [1, §8], with its lemma.

* **Random self-reduction** [1, §8.1]: if the RSA assumption holds, so does its many-challenge
  form. The reduction `SelfReduction` samples a uniform unit `r_i` for every index once, answers
  the `i`-th challenge with `Y · r_i^e`, and a root `X` of it by `rsa.check(X · r_i⁻¹)`. Against
  the RSA libraries both sides are sampled functions of the key and the challenges, under the
  law of `rsa*` and under that of the self-reduction. The challenges of `rsa*` are independent
  uniform units with probability `c^n`, and those of the self-reduction with probability `c`, for
  `c = φ(N)/N ≥ 1 - δ`; so the two laws are within `(n + 1) δ` in `ℓ¹`, after scaling the second
  by `(1 - δ)^(n-1)`, and a distinguisher decides on a sampled function on average.
* **RSA-PSS** [1, §8.2]: if the RSA assumption holds, RSA-PSS,

  $$\mathsf{Sign}((N, d), m):\ R \leftarrow \{0,1\}^\lambda,\ S := \mathsf{RO}(m \,\|\, R)^d
  \bmod N; \qquad \mathsf{Verify}((N, e), m, (R, S)) = [\mathsf{RO}(m \,\|\, R) = S^e \bmod N],$$

  is a secure signature scheme in the random-oracle model: `sig-real+ro` substitutes for
  `sig-fake` on it, the converter that records the signatures it returns and accepts exactly
  those. `sig-real+ro` is the real system of RSA-PSS: a key `(N, e, d)` sampled once, an oracle
  with values uniform in `ℤ_N` sampled once for it, and the scheme's oracles under them beside
  the oracle, `sample (N, e, d) ← keyGen; RSA-PSS(N, e, d) ∥ RO(N)`, at the interface of the
  libraries (`SignatureSchemeRO.Forward`). The reduction `𝓡` to the many-challenge
  assumption programs the oracle: at a signature query at a new point `m ‖ R` it sets
  `RO(m ‖ R) := S^e` for a uniform `S` and returns `(R, S)`, at a point it programmed it returns
  the root it stored, and at any other new point it answers a challenge of `rsa*`, verifying
  there through `check*`. The proof is the chain
  `sig-real+ro ≈ 𝓡 • rsa*-real ≃ 𝓡 • rsa*-fake ≈ sig-fake`. The four libraries are one automaton
  with the oracle sampled lazily (`Lazy.step`), with their signing and verification rules: the
  libraries along the kernel that fills the rest of the oracle, the reduction along a map of
  states. The reduction and each library step alike until a signature query hits a point the
  oracle or a verification query defined, which `R` does with probability at most
  `(q_ro + q_ver) / |Salt|` at each signature query, so each `≈` loses
  `q_sign (q_ro + q_ver) / |Salt|`
  (`Lazy.distance_le`, from `Interface.Resource.distance_ofProbAutomaton_le`).

Salts `R` range over a finite type `Salt`, of which the notes' `{0,1}^λ` is an instance, and the
oracle is a uniform function of `(m, R) ∈ M × Salt` with values in `ℤ_N`. The modulus `N` is
sampled while interface alphabets are fixed, so the residues of every modulus share the type
`RSA.Residue bits`, which holds `ℤ_N` as the representatives `0, …, N − 1` of `ZMod N`.
Signatures range over it and verification also checks that `S` is a residue modulo `N`; the
bounds of [1] are asymptotic, and the concrete losses here are those of the arguments above. The
self-reduction is proved with the challenges indexed by their number (`RSAStar.Indexed`), which
`RSAStar.Count` gives out in order. The notes' library `sig-real+ro` samples the key and an
oracle for every modulus and answers at the key's `N`; it is `sig-real+ro`, since at each key and
oracle the two are the same automaton and the oracle at `N` is a coordinate of the oracle for
every modulus. The notes' `sig-fake` is the converter `sig-fake` on `sig-real+ro`, along the kernel that keeps the
key, the oracle and the recorded signatures.

Upstream candidates, for `Commons.Definitions.Signature`: `SigningRO`, `SignatureScheme.FakeRO`
and its steps on an automaton (`SignatureScheme.FakeRO.outcome_pk`, …), `SignatureSchemeRO`,
`SignatureSchemeRO.Fixed`, `SignatureSchemeRO.Real`, `SignatureSchemeRO.Forward` and its typing,
and their steps on automata (`SignatureSchemeRO.Fixed.step_sign`,
`SignatureSchemeRO.Forward.step_pk`, …); for `Common/ProbAutomaton`: `SimulationOn.refl`,
`FreshSampling.ofFunction`, `ProbStep.belief_bindK` and
`Interface.Resource.ofProbAutomaton_fTransform`.

## Main definitions

* `SigningRO PK M Sig A H`, `SignatureScheme.FakeRO`: the interface of a signature system with an
  oracle, and `sig-fake` as a converter on it
* `SignatureSchemeRO K PK M Sig A H`: a signature scheme in the random-oracle model
* `SignatureSchemeRO.Fixed scheme key RO`: its oracles under a fixed key and oracle
* `SignatureSchemeRO.Real scheme keyGen oracle`: its real system, the key and the oracle sampled
  once, the oracle's law depending on the public key
* `SignatureSchemeRO.Forward`, `SignatureSchemeRO.Forward.perLabel`: the scheme and the oracle
  beside it at one interface, at per-port budgets
* `SigRO.perPort bits Salt M q`, `SigRO.Input`, `SigRO.Output`: the interface of the RSA-PSS
  libraries
* `residueOracle`, `residueOracles`: an oracle with values uniform in `ℤ_N`, for one modulus and
  for every modulus
* `scheme Salt M`: RSA-PSS in the random-oracle model
* `SigReal`: `sig-real+ro`, the real system of RSA-PSS
* `SigReal.Library`, `SigFake`: the notes' `sig-real+ro` and `sig-fake`
* `SelfReduction`, `SelfReduction.perLabel`: the random self-reduction, at per-port budgets
* `selfChallengeLaw`: the challenges `Y · r_i^e` of the self-reduction modulo `N`
* `starLaw`, `selfLaw`: the key and the challenges of `rsa*` and of the self-reduction
* `𝓡`, `𝓡.perLabel`: the reduction to the many-challenge assumption, at per-port budgets
* `Lazy.State`, `Lazy.step`: the libraries and the reduction with the oracle sampled lazily
* `Lazy.signLibrary`, `Lazy.signReduction`, `Lazy.verifyReal`, `Lazy.verifyFake`,
  `Lazy.verifyReduction`: their signing and verification rules
* `Lazy.oracle`: the oracle of a table, the rest sampled uniformly

## Main results

* `SelfReduction.smul_real`, `SelfReduction.smul_fake`: the self-reduction on the RSA libraries
  is the indexed many-challenge libraries on its challenges
* `sum_abs_starLaw_sub_selfLaw_le`: the challenges of `rsa*` and of the self-reduction are close
* `rsa_self_reduction_indexed`: the self-reduction with indexed challenges
* `rsa_self_reduction`: the RSA assumption gives its many-challenge form
* `SigReal.eq_library`: `sig-real+ro` is the notes' library
* `SigFake.perPort_eq_fakeRO`: `sig-fake` is the converter `sig-fake` on `sig-real+ro`
* `SigReal.eq_lazy`, `SigFake.perPort_eq_lazy`, `𝓡.smul_real`, `𝓡.smul_fake`: the four
  libraries of the chain as the lazy automaton
* `Lazy.distance_le`: the reduction and a library verifying alike are identical until bad
* `𝓡.distance_real`, `𝓡.distance_fake`: the two programming steps
* `rsa_pss_of_rsaStar`: RSA-PSS from the many-challenge assumption
* `composed_loss_eq`: the loss of the two reductions composed
* `rsa_pss`: RSA-PSS from the RSA assumption
* `rsa_pss_bits`: the notes' statement, at salts in `{0,1}^λ`

## References

1. The symmetric proof ladder, *Security proofs in the style of The Joy of Cryptography*,
   `proof-ladders/symmetric-ladder`, `Notes/selfcontained.tex`.
-/

/-! ## Upstream candidate (Commons.Definitions.Signature)

The interface of a signature system with an oracle, and `sig-fake` as a converter on it: it
records the signatures it returns and verifies by lookup. -/

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

interface SigningRO(PK M Sig A H : Type) [Fintype PK] [Fintype M] [Fintype Sig] [Fintype A] [Fintype H]
  pk() → PK
  sign(m : M) → Sig
  ver(m : M, σ : Sig) → Bool
  ro(a : A) → H

-- `sig-fake` [1, §8.2]: forward `pk()` and `ro(a)`; `sign(m)` returns `σ ← sig.sign(m)` and adds
-- `(m, σ)` to `𝒮`; `ver(m, σ)` returns whether `(m, σ) ∈ 𝒮`.
converter SignatureScheme.FakeRO(PK M Sig A H : Type) [Fintype PK] [Fintype M] [Fintype Sig] [Fintype A] [Fintype H] [DecidableEq M] [DecidableEq Sig] : SigningRO PK M Sig A H
  inside sig : SigningRO PK M Sig A H
  initialize
    signed ← ([] : List (M × Sig))
  on pk() → PK
    pk ← sig.pk()
    return pk
  on sign(m : M) → Sig
    σ ← sig.sign(m)
    signed ← signed ++ [(m, σ)]
    return σ
  on ver(m : M, σ : Sig) → Bool
    return decide ((m, σ) ∈ signed)
  on ro(a : A) → H
    h ← sig.ro(a)
    return h

section FakeROSteps

open Probability.Distribution

variable {PK M Sig A H : Type} [Fintype PK] [Fintype M] [Fintype Sig] [Fintype A] [Fintype H]
  [DecidableEq M] [DecidableEq Sig] {R : Type}
  (stepR : ProbStep R SigningRO.Port (SigningRO.Input M Sig A) (SigningRO.Output PK Sig H))

set_option hygiene false in
/-- `sig-fake` on the probabilistic automaton `stepR`. -/
local notation "fakeStep(" stepR ")" =>
  (SignatureScheme.FakeRO.body PK M Sig A H).probCombine stepR
    (SignatureScheme.FakeRO.bound_spec PK M Sig A H)

/-- `sig-fake` on an automaton: `pk()` is forwarded. -/
lemma SignatureScheme.FakeRO.outcome_pk (s : Option (List (M × Sig))) (r : R)
    (u : SigningRO.Input M Sig A .pk) :
    (fakeStep(stepR)).outcome (s, r) ⟨.pk, u⟩ =
      fTransform (fun p => ((some (s.getD []), p.1), p.2)) (stepR.outcome r ⟨.pk, u⟩) := by
  rw [ProbStep.outcome, Program.probCombine_val,
    show SignatureScheme.FakeRO.bound PK M Sig A H = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.pk, u⟩)
      (by cases s <;> simp [SignatureScheme.FakeRO.body, callProg]),
    fTransform_bindK, fTransform_eq_bindK]
  refine bindK_congr fun p hp => ?_
  obtain ⟨y, hy⟩ := Program.mem_support_outcome hp
  rw [Program.probInvoke_inl (a := (some (s.getD []), y))
    (by cases s <;> simp [SignatureScheme.FakeRO.body, callProg, returnProg, hy])]
  simp [fTransform, ProbStep.tagged, hy]

/-- `sig-fake` on an automaton: `sign(m)` is forwarded and its signature recorded. -/
lemma SignatureScheme.FakeRO.outcome_sign (s : Option (List (M × Sig))) (r : R) (m : M) :
    (fakeStep(stepR)).outcome (s, r) ⟨.sign, m⟩ =
      fTransform (fun p => ((some (s.getD [] ++ match p.2 with
          | ⟨.sign, σ⟩ => [(m, σ)]
          | _ => []), p.1), p.2)) (stepR.outcome r ⟨.sign, m⟩) := by
  rw [ProbStep.outcome, Program.probCombine_val,
    show SignatureScheme.FakeRO.bound PK M Sig A H = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.sign, m⟩)
      (by cases s <;> simp [SignatureScheme.FakeRO.body, callProg]),
    fTransform_bindK, fTransform_eq_bindK]
  refine bindK_congr fun p hp => ?_
  obtain ⟨y, hy⟩ := Program.mem_support_outcome hp
  rw [Program.probInvoke_inl (a := (some (s.getD [] ++ [(m, y)]), y))
    (by cases s <;> simp [SignatureScheme.FakeRO.body, callProg, returnProg, hy])]
  simp [fTransform, ProbStep.tagged, hy]

/-- `sig-fake` on an automaton: `ver(m, σ)` is whether `(m, σ)` was recorded. -/
lemma SignatureScheme.FakeRO.outcome_ver (s : Option (List (M × Sig))) (r : R) (m : M)
    (σ : Sig) :
    (fakeStep(stepR)).outcome (s, r) ⟨.ver, (m, σ)⟩ =
      Finsupp.single ((some (s.getD []), r),
        (⟨.ver, decide ((m, σ) ∈ s.getD [])⟩ : Σ i, SigningRO.Output PK Sig H i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (s.getD []), decide ((m, σ) ∈ s.getD [])))
      (by cases s <;> simp [SignatureScheme.FakeRO.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- `sig-fake` on an automaton: `ro(a)` is forwarded. -/
lemma SignatureScheme.FakeRO.outcome_ro (s : Option (List (M × Sig))) (r : R) (a : A) :
    (fakeStep(stepR)).outcome (s, r) ⟨.ro, a⟩ =
      fTransform (fun p => ((some (s.getD []), p.1), p.2)) (stepR.outcome r ⟨.ro, a⟩) := by
  rw [ProbStep.outcome, Program.probCombine_val,
    show SignatureScheme.FakeRO.bound PK M Sig A H = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.ro, a⟩)
      (by cases s <;> simp [SignatureScheme.FakeRO.body, callProg]),
    fTransform_bindK, fTransform_eq_bindK]
  refine bindK_congr fun p hp => ?_
  obtain ⟨y, hy⟩ := Program.mem_support_outcome hp
  rw [Program.probInvoke_inl (a := (some (s.getD []), y))
    (by cases s <;> simp [SignatureScheme.FakeRO.body, callProg, returnProg, hy])]
  simp [fTransform, ProbStep.tagged, hy]

end FakeROSteps

/-! ## Upstream candidate (Commons.Definitions.Signature)

A signature scheme in the random-oracle model, its oracles under a fixed key and oracle, its real
system, and the converter presenting the scheme and the oracle beside it at one interface. -/

/-- **A signature scheme in the random-oracle model**, with keys `K`, public keys `PK`, messages
`M`, signatures `Sig` and the oracle `RO : A → H`: the public key of a key, signing with a key and
verification with a public key, both with the oracle. -/
structure SignatureSchemeRO (K PK M Sig A H : Type) where
  /-- The public key of a key. -/
  publicKey : K → PK
  /-- Signing `S^RO`. -/
  sign : K → (A → H) → M → Distribution.ProbDist Sig
  /-- Verification `V^RO`. -/
  verify : PK → (A → H) → M → Sig → Bool

-- The oracles of a signature scheme under the key `key` and the oracle `RO`: `publicKey()`
-- returns the public key; `sign(m)` returns `σ ← S^RO(key, m)`; `verify(m, σ)` returns
-- `V^RO(pk, m, σ)`.
system SignatureSchemeRO.Fixed(K PK M Sig A H : Type) [Fintype PK] [Fintype M] [Fintype Sig] [DecidableEq M] (scheme : SignatureSchemeRO K PK M Sig A H) (key : K) (RO : A → H) : Signing PK M Sig
  on publicKey() → PK
    return scheme.publicKey key
  on sign(message : M) → Sig
    signatures ←$ Distribution.ProbDist.pi (scheme.sign key RO)
    return signatures message
  on verify(message : M, signature : Sig) → Bool
    return scheme.verify (scheme.publicKey key) RO message signature

-- The scheme and the oracle beside it at one interface: forward `pk()`, `sign(m)` and
-- `ver(m, σ)` to the scheme, and `ro(a)` to the oracle.
converter SignatureSchemeRO.Forward(PK M Sig A H : Type) [Fintype PK] [Fintype M] [Fintype Sig] [Fintype A] [Fintype H] : SigningRO PK M Sig A H
  inside sig : Signing PK M Sig
  inside oracle : Evaluation A H
  on pk() → PK
    pk ← sig.publicKey()
    return pk
  on sign(m : M) → Sig
    σ ← sig.sign(m)
    return σ
  on ver(m : M, σ : Sig) → Bool
    valid ← sig.verify(m, σ)
    return valid
  on ro(a : A) → H
    h ← oracle.eval(a)
    return h

noncomputable section

open SystemAlgebra.Interface CategoryTheory

variable {K PK M Sig A H : Type} [Fintype PK] [Fintype M] [Fintype Sig] [Fintype A] [Fintype H]

/-- **The real system of a signature scheme in the random-oracle model**: a key `key ← keyGen`,
an oracle `RO ← oracle pk` for its public key `pk`, both sampled once, and the scheme's oracles
under `key` and `RO` beside `RO`. -/
def SignatureSchemeRO.Real [DecidableEq M] (scheme : SignatureSchemeRO K PK M Sig A H)
    (keyGen : Distribution.ProbDist K) (oracle : PK → Distribution.ProbDist (A → H))
    (q : Signing.Port → ℕ) (n : ℕ) :
    Resource ((Signing.perPort PK M Sig q).tensor (Evaluation A H n)) :=
  Resource.sample keyGen.1 fun key => Resource.sample (oracle (scheme.publicKey key)).1 fun RO =>
    SignatureSchemeRO.Fixed.perPort K PK M Sig A H scheme key RO ∥ Resource.ofFunction fun _ => RO

/-- The inside budget of `SignatureSchemeRO.Forward` at the scheme: each port at the budget of the
procedure calling it. -/
abbrev SignatureSchemeRO.Forward.insideBudget (q : SigningRO.Port → ℕ) : Signing.Port → ℕ
  | .publicKey => q .pk
  | .sign => q .sign
  | .verify => q .ver

/-- The inside interface of `SignatureSchemeRO.Forward`: the scheme beside the oracle. -/
abbrev SignatureSchemeRO.Forward.inside (PK M Sig A H : Type) [Fintype PK] [Fintype M]
    [Fintype Sig] [Fintype A] [Fintype H] (q : SigningRO.Port → ℕ) : Interface :=
  (Signing.perPort PK M Sig (SignatureSchemeRO.Forward.insideBudget q)).tensor
    (Evaluation A H (q .ro))

/-- The inside calls of `SignatureSchemeRO.Forward` per procedure: one, at its own port. -/
def SignatureSchemeRO.Forward.calls : SigningRO.Port → Signing.Port ⊕ Evaluation.Port → ℕ
  | .pk, .inl .publicKey => 1
  | .sign, .inl .sign => 1
  | .ver, .inl .verify => 1
  | .ro, .inr .eval => 1
  | _, _ => 0

/-- `SignatureSchemeRO.Forward` calls each inside label at most `SignatureSchemeRO.Forward.calls`
times per procedure. -/
lemma SignatureSchemeRO.Forward.labelBounded :
    (SignatureSchemeRO.Forward.body PK M Sig A H).LabelBounded
      SignatureSchemeRO.Forward.calls := by
  intro s o u
  cases o <;> simp only [SignatureSchemeRO.Forward.body] <;> cases s <;> dsimp only <;>
    repeat' (first
      | exact Program.labelCallBound_return _ _
      | (refine Program.labelCallBound_call _ _ _ (by decide) fun y => ?_))

/-- The inside interface admits the per-label budget of `SignatureSchemeRO.Forward`. -/
lemma SignatureSchemeRO.Forward.admits (q : SigningRO.Port → ℕ) :
    (SignatureSchemeRO.Forward.inside PK M Sig A H q).AdmitsLabelBudget
      fun j => ∑ o, SignatureSchemeRO.Forward.calls o j * q o := by
  refine ((portBudget_admitsLabelBudget _ _ _ _).tensor (queryBudget_admitsLabelBudget _ _ _
    (fun _ => q .ro) (by simp))).mono fun j => ?_
  rcases j with (_ | _ | _) | _ <;>
    simp [Finset.univ, Fintype.elems, SignatureSchemeRO.Forward.calls]

/-- **`SignatureSchemeRO.Forward` at per-port budgets.** -/
def SignatureSchemeRO.Forward.perLabel (q : SigningRO.Port → ℕ) :
    SigningRO.perPort PK M Sig A H q ⟶ SignatureSchemeRO.Forward.inside PK M Sig A H q :=
  Converter.ofLabelBoundedProgram (A := SigningRO.perPort PK M Sig A H q)
    (B := SignatureSchemeRO.Forward.inside PK M Sig A H q) none
    (SignatureSchemeRO.Forward.body PK M Sig A H)
    (SignatureSchemeRO.Forward.bound_spec PK M Sig A H) SignatureSchemeRO.Forward.calls
    SignatureSchemeRO.Forward.labelBounded q (fun _ hd => hd.2)
    (SignatureSchemeRO.Forward.admits q)

open Probability.Distribution

section FixedSteps

variable [DecidableEq M] (scheme : SignatureSchemeRO K PK M Sig A H) (key : K) (RO : A → H)

set_option hygiene false in
/-- The oracles of the scheme under `key` and `RO`, sampling afresh. -/
local notation "fixedStep" =>
  (SignatureSchemeRO.Fixed.body K PK M Sig A H scheme key RO).probCombine
    (ProbStep.fresh (SignatureSchemeRO.Fixed.law1 K PK M Sig A H scheme key RO))
    (SignatureSchemeRO.Fixed.bound_spec K PK M Sig A H scheme key RO)

omit [Fintype A] [Fintype H] in
/-- The scheme's oracles sampling afresh: `publicKey()` is the public key. -/
lemma SignatureSchemeRO.Fixed.step_publicKey (s : Option Unit) (u : Unit) :
    (fixedStep (s, ()) .publicKey u).1 =
      Finsupp.single ((some (), ()), scheme.publicKey key) 1 := by
  rw [Program.probCombine_val]
  cases s <;> rw [Program.probInvoke_inl (o := Signing.Port.publicKey)
    (a := (some (), scheme.publicKey key)) (by simp [SignatureSchemeRO.Fixed.body, returnProg])]

omit [Fintype A] [Fintype H] in
/-- The scheme's oracles sampling afresh: `sign(m)` is a signature `σ ← S^RO(key, m)`. -/
lemma SignatureSchemeRO.Fixed.step_sign (s : Option Unit) (m : M) :
    (fixedStep (s, ()) .sign m).1 =
      fTransform (fun σ => ((some (), ()), σ)) (scheme.sign key RO m).1 := by
  rw [Program.probCombine_val,
    show SignatureSchemeRO.Fixed.bound K PK M Sig A H scheme key RO = 0 + 1 from rfl]
  cases s <;>
  · rw [Program.probInvoke_succ_inr (q := ⟨(), ()⟩)
      (by simp [SignatureSchemeRO.Fixed.body, callProg])]
    simp only [ProbStep.outcome, ProbStep.fresh, fTransform_fTransform, bindK_fTransform,
      Function.comp_def]
    refine (bindK_congr (g := fun t : M → Sig => Finsupp.single ((some (), ()), t m) 1)
      fun t _ => ?_).trans ?_
    · rw [Program.probInvoke_inl (o := Signing.Port.sign) (a := (some (), t m))
        (by simp [SignatureSchemeRO.Fixed.body, callProg, returnProg, ProbStep.tagged])]
    exact (bindK_pi_apply (fun m => (scheme.sign key RO m).1) (fun m => (scheme.sign key RO m).2.2)
      m fun σ => Finsupp.single ((some (), ()), σ) 1).trans (bindK_single_comp _ _)

omit [Fintype A] [Fintype H] in
/-- The scheme's oracles sampling afresh: `verify(m, σ)` is `V^RO(pk, m, σ)`. -/
lemma SignatureSchemeRO.Fixed.step_verify (s : Option Unit) (m : M) (σ : Sig) :
    (fixedStep (s, ()) .verify (m, σ)).1 =
      Finsupp.single ((some (), ()), scheme.verify (scheme.publicKey key) RO m σ) 1 := by
  rw [Program.probCombine_val]
  cases s <;> rw [Program.probInvoke_inl (o := Signing.Port.verify)
    (a := (some (), scheme.verify (scheme.publicKey key) RO m σ))
    (by simp [SignatureSchemeRO.Fixed.body, returnProg])]

end FixedSteps

section ForwardSteps

variable {S₁ S₂ : Type} (f : ProbStep S₁ (Signing PK M Sig 0).I (Signing PK M Sig 0).X
    (Signing PK M Sig 0).Y)
  (g : ProbStep S₂ (Evaluation A H 0).I (Evaluation A H 0).X (Evaluation A H 0).Y)

set_option hygiene false in
/-- `SignatureSchemeRO.Forward` on the automata `f` of the scheme and `g` of the oracle side by
side. -/
local notation "forwardStep" =>
  (SignatureSchemeRO.Forward.body PK M Sig A H).probCombine (ProbStep.parallel f g)
    (SignatureSchemeRO.Forward.bound_spec PK M Sig A H)

/-- `SignatureSchemeRO.Forward` on automata: `pk()` is forwarded to `publicKey()`. -/
lemma SignatureSchemeRO.Forward.step_pk (s : Option Unit) (a : S₁) (b : S₂) (u : Unit) :
    (forwardStep (s, (a, b)) .pk u).1 =
      fTransform (fun p => ((some (), (p.1, b)), p.2)) (f a .publicKey ()).1 := by
  rw [Program.probCombine_val,
    show SignatureSchemeRO.Forward.bound PK M Sig A H = 0 + 1 from rfl]
  cases s <;>
  · rw [Program.probInvoke_succ_inr (q := ⟨.inl .publicKey, ()⟩)
      (by simp [SignatureSchemeRO.Forward.body, callProg]), ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, fTransform_fTransform, bindK_fTransform, Function.comp_def]
    rw [fTransform_eq_bindK]
    refine bindK_congr fun p _ => ?_
    rw [Program.probInvoke_inl (o := SigningRO.Port.pk) (a := (some (), p.2))
      (by simp [SignatureSchemeRO.Forward.body, callProg, returnProg, ProbStep.tagged,
        ProbStep.inlReply])]
    rfl

/-- `SignatureSchemeRO.Forward` on automata: `sign(m)` is forwarded. -/
lemma SignatureSchemeRO.Forward.step_sign (s : Option Unit) (a : S₁) (b : S₂) (m : M) :
    (forwardStep (s, (a, b)) .sign m).1 =
      fTransform (fun p => ((some (), (p.1, b)), p.2)) (f a .sign m).1 := by
  rw [Program.probCombine_val,
    show SignatureSchemeRO.Forward.bound PK M Sig A H = 0 + 1 from rfl]
  cases s <;>
  · rw [Program.probInvoke_succ_inr (q := ⟨.inl .sign, m⟩)
      (by simp [SignatureSchemeRO.Forward.body, callProg]), ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, fTransform_fTransform, bindK_fTransform, Function.comp_def]
    rw [fTransform_eq_bindK]
    refine bindK_congr fun p _ => ?_
    rw [Program.probInvoke_inl (o := SigningRO.Port.sign) (a := (some (), p.2))
      (by simp [SignatureSchemeRO.Forward.body, callProg, returnProg, ProbStep.tagged,
        ProbStep.inlReply])]
    rfl

/-- `SignatureSchemeRO.Forward` on automata: `ver(m, σ)` is forwarded to `verify(m, σ)`. -/
lemma SignatureSchemeRO.Forward.step_ver (s : Option Unit) (a : S₁) (b : S₂) (m : M)
    (σ : Sig) :
    (forwardStep (s, (a, b)) .ver (m, σ)).1 =
      fTransform (fun p => ((some (), (p.1, b)), p.2)) (f a .verify (m, σ)).1 := by
  rw [Program.probCombine_val,
    show SignatureSchemeRO.Forward.bound PK M Sig A H = 0 + 1 from rfl]
  cases s <;>
  · rw [Program.probInvoke_succ_inr (q := ⟨.inl .verify, (m, σ)⟩)
      (by simp [SignatureSchemeRO.Forward.body, callProg]), ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, fTransform_fTransform, bindK_fTransform, Function.comp_def]
    rw [fTransform_eq_bindK]
    refine bindK_congr fun p _ => ?_
    rw [Program.probInvoke_inl (o := SigningRO.Port.ver) (a := (some (), p.2))
      (by simp [SignatureSchemeRO.Forward.body, callProg, returnProg, ProbStep.tagged,
        ProbStep.inlReply])]
    rfl

/-- `SignatureSchemeRO.Forward` on automata: `ro(a)` is forwarded to the oracle. -/
lemma SignatureSchemeRO.Forward.step_ro (s : Option Unit) (a : S₁) (b : S₂) (x : A) :
    (forwardStep (s, (a, b)) .ro x).1 =
      fTransform (fun p => ((some (), (a, p.1)), p.2)) (g b .eval x).1 := by
  rw [Program.probCombine_val,
    show SignatureSchemeRO.Forward.bound PK M Sig A H = 0 + 1 from rfl]
  cases s <;>
  · rw [Program.probInvoke_succ_inr (q := ⟨.inr .eval, x⟩)
      (by simp [SignatureSchemeRO.Forward.body, callProg]), ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, fTransform_fTransform, bindK_fTransform, Function.comp_def]
    rw [fTransform_eq_bindK]
    refine bindK_congr fun p _ => ?_
    rw [Program.probInvoke_inl (o := SigningRO.Port.ro) (a := (some (), p.2))
      (by simp [SignatureSchemeRO.Forward.body, callProg, returnProg, ProbStep.tagged,
        ProbStep.inrReply])]
    rfl

end ForwardSteps

end

end Commons

/-! ## Upstream candidate (Common/ProbAutomaton)

A function as fresh sampling, and an automaton with a sampled initial state as the mixture of the
automata started at its samples. -/

namespace SystemAlgebra

open Probability Probability.Distribution

/-- **The identity simulation** of a probabilistic step. -/
noncomputable def SimulationOn.refl {S I : Type} {X Y : I → Type} (E : List (Σ i, X i) → Prop)
    (step : ProbStep S I X Y) : SimulationOn E step step where
  kernel := ProbStep.idKernel S
  inv := fun _ _ => True
  pres := fun _ _ _ _ _ _ _ => trivial
  sim := fun _ s x _ _ => ProbStep.simulatesAt_refl step s x

/-- **A function is fresh sampling**: it samples nothing. -/
noncomputable def FreshSampling.ofFunction {B : Interface} (g : ∀ i, B.X i → B.Y i) :
    FreshSampling B (Interface.Resource.ofFunction g) where
  stepD := fun _ i x => ((), g i x)
  initD := Distribution.ProbDist.single ()
  eq := Interface.Resource.ofFunction_eq_ofAutomaton g
  stepRF := ProbStep.ofDeterministic fun _ i x => ((), g i x)
  initRF := ()
  stepF := ProbStep.ofDeterministic fun _ i x => ((), g i x)
  initF := ()
  toTable := SimulationOn.refl _ _
  toFresh := SimulationOn.refl _ _
  inv_table := trivial
  inv_fresh := trivial
  init_table := rfl
  init_fresh := rfl

/-- **The forward algorithm is linear** in the initial law. -/
lemma ProbStep.belief_bindK {S I : Type} {X Y : I → Type} (step : ProbStep S I X Y)
    (D : Domain (Σ i, X i) (Σ i, Y i)) {K : Type} (μ : Distribution K) (init : K → Distribution S)
    (h : List ((Σ i, X i) × (Σ i, Y i))) :
    step.belief D (bindK μ init) h = bindK μ fun k => step.belief D (init k) h := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h e ih =>
    obtain ⟨x, y⟩ := e
    simp only [ProbStep.belief_snoc]
    split_ifs
    · rw [ih]
      simp only [ProbStep.transition, bindK_bindK]
    · exact (bindK_zero_right μ).symm

/-- **A probabilistic automaton with a sampled initial state** samples the automaton started
there. -/
lemma Interface.Resource.ofProbAutomaton_fTransform {T : Interface} {S K : Type}
    (step : ProbStep S T.I T.X T.Y) (P : Distribution K) [Distribution.IsProbability P]
    (init : K → S) :
    Interface.Resource.ofProbAutomaton T step ⟨fTransform init P,
        fTransform_isProbDist _ (Distribution.IsProbability.isProbDist P)⟩ =
      Interface.Resource.sample P fun k =>
        Interface.Resource.ofProbAutomaton T step (Distribution.ProbDist.single (init k)) := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [Interface.Resource.sample_mass]
  show RandomSystem.ofProbAutomaton _ _ _ h = ∑ k ∈ P.support, P k *
    RandomSystem.ofProbAutomaton _ _ (Distribution.ProbDist.single (init k)) h
  simp only [RandomSystem.ofProbAutomaton_apply]
  rw [show (fTransform init P) = bindK P fun k => Finsupp.single (init k) 1 from
    fTransform_eq_bindK _ _, ProbStep.belief_bindK, weight_bindK]
  rfl

end SystemAlgebra

namespace ProofLadders.RSAPSS

open Commons Probability SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface CategoryTheory
open scoped SystemAlgebra SystemAlgebra.DSL

/-- The interface of the RSA-PSS libraries at the budget `q` per port: the public keys `(N, e)`,
the messages `M`, the signatures `(R, S)`, and the oracle on `M × Salt` with values in the
residues. -/
abbrev SigRO.perPort (bits : ℕ) (Salt M : Type) [Fintype Salt] [Fintype M]
    (q : SigningRO.Port → ℕ) : Interface :=
  SigningRO.perPort (RSA.Residue bits × RSA.Residue bits) M (Salt × RSA.Residue bits) (M × Salt)
    (RSA.Residue bits) q

/-- The inputs of the RSA-PSS libraries. -/
abbrev SigRO.Input (bits : ℕ) (Salt M : Type) [Fintype Salt] [Fintype M] :
    SigningRO.Port → Type :=
  SigningRO.Input M (Salt × RSA.Residue bits) (M × Salt)

/-- The outputs of the RSA-PSS libraries. -/
abbrev SigRO.Output (bits : ℕ) (Salt : Type) [Fintype Salt] : SigningRO.Port → Type :=
  SigningRO.Output (RSA.Residue bits × RSA.Residue bits) (Salt × RSA.Residue bits)
    (RSA.Residue bits)

variable {bits : ℕ}

noncomputable section

/-- **The oracle with values uniform in `ℤ_N`**: independent uniform residues modulo `N` at
every point. -/
def residueOracle (A : Type) [Fintype A] [DecidableEq A] (N : RSA.Residue bits) :
    Distribution.ProbDist (A → RSA.Residue bits) :=
  Distribution.ProbDist.pi fun _ : A => RSA.residue N

/-- **An oracle with values in `ℤ_N`**, for every modulus `N`: independent oracles with values
uniform in `ℤ_N`. -/
def residueOracles (A : Type) [Fintype A] [DecidableEq A] :
    Distribution.ProbDist (RSA.Residue bits → A → RSA.Residue bits) :=
  Distribution.ProbDist.pi (residueOracle A)

/-- **RSA-PSS** [1, §8.2] in the random-oracle model, with the keys `(N, e, d)`: the public key
is `(N, e)`; `Sign((N, d), m)` samples `R ← Salt` and returns `(R, RO(m ‖ R)^d mod N)`, and
`Verify((N, e), m, (R, S))` checks that `S` is a residue modulo `N` and `RO(m ‖ R) = S^e mod N`. -/
def scheme (Salt : Type) [Fintype Salt] [Nonempty Salt] (M : Type) :
    SignatureSchemeRO (RSA.Key bits) (RSA.Residue bits × RSA.Residue bits) M
      (Salt × RSA.Residue bits) (M × Salt) (RSA.Residue bits) where
  publicKey key := (key.N, key.e)
  sign key RO m := Distribution.ProbDist.map (fun R => (R, key.pow (RO (m, R)) key.d.val))
    (DSL.uniform Salt)
  verify pk RO m σ := decide (σ.2.val < pk.1.val ∧ RO (m, σ.1) = RSA.powMod pk.1 pk.2 σ.2)

/-- **`sig-real+ro`** [1, §8.2]: the real system of RSA-PSS, a key `(N, e, d) ← keyGen` and an
oracle with values uniform in `ℤ_N` sampled once, and the scheme's oracles under them beside the
oracle, at the interface of the libraries. -/
def SigReal (Salt : Type) [Fintype Salt] [Nonempty Salt] [DecidableEq Salt] (M : Type)
    [Fintype M] [DecidableEq M] (keyGen : Distribution.ProbDist (RSA.Key bits))
    (q : SigningRO.Port → ℕ) : Resource (SigRO.perPort bits Salt M q) :=
  SignatureSchemeRO.Forward.perLabel q •
    SignatureSchemeRO.Real (scheme Salt M) keyGen (fun pk => residueOracle (M × Salt) pk.1)
      (SignatureSchemeRO.Forward.insideBudget q) (q .ro)

-- The notes' `sig-real+ro`: `(N, e, d) := RSA.KeyGen()`; `pk()` returns `(N, e)`; `sign(m)`
-- returns `Sign(sk, m)`; `ver(m, (R, S))` returns `Verify(pk, m, (R, S))`; `ro(A)` returns
-- `RO(A)`.
system SigReal.Library(Salt : Type) [Fintype Salt] [Nonempty Salt] [DecidableEq Salt] (M : Type) [Fintype M] [DecidableEq M] (keyGen : Distribution.ProbDist (RSA.Key bits)) : SigningRO (RSA.Residue bits × RSA.Residue bits) M (Salt × RSA.Residue bits) (M × Salt) (RSA.Residue bits)
  initialize
    key ←$ keyGen
    ROs ←$ residueOracles (bits := bits) (M × Salt)
  on pk() → RSA.Residue bits × RSA.Residue bits
    return (key.N, key.e)
  on sign(m : M) → Salt × RSA.Residue bits
    R ←$ 𝒰[Salt]
    return (R, key.pow (ROs key.N (m, R)) key.d.val)
  on ver(m : M, R : Salt, S : RSA.Residue bits) → Bool
    return decide (S.val < key.N.val ∧ ROs key.N (m, R) = key.pow S key.e.val)
  on ro(m : M, R : Salt) → RSA.Residue bits
    return ROs key.N (m, R)

-- `sig-fake`: as `sig-real+ro`, but `sign(m)` adds `(m, R, S)` to `𝒮`, and `ver(m, (R, S))`
-- returns whether `(m, R, S) ∈ 𝒮`.
system SigFake(Salt : Type) [Fintype Salt] [Nonempty Salt] [DecidableEq Salt] (M : Type) [Fintype M] [DecidableEq M] (keyGen : Distribution.ProbDist (RSA.Key bits)) : SigningRO (RSA.Residue bits × RSA.Residue bits) M (Salt × RSA.Residue bits) (M × Salt) (RSA.Residue bits)
  initialize
    key ←$ keyGen
    ROs ←$ residueOracles (bits := bits) (M × Salt)
    signed ← ([] : List (M × Salt × RSA.Residue bits))
  on pk() → RSA.Residue bits × RSA.Residue bits
    return (key.N, key.e)
  on sign(m : M) → Salt × RSA.Residue bits
    R ←$ 𝒰[Salt]
    signed ← signed ++ [(m, R, key.pow (ROs key.N (m, R)) key.d.val)]
    return (R, key.pow (ROs key.N (m, R)) key.d.val)
  on ver(m : M, R : Salt, S : RSA.Residue bits) → Bool
    return decide ((m, R, S) ∈ signed)
  on ro(m : M, R : Salt) → RSA.Residue bits
    return ROs key.N (m, R)

/-! ## The random self-reduction

The reduction calls `rsa.challenge()` once per query and `rsa.check` once per check, beside its
source of units: its program is bounded per label, `Converter.ofLabelBoundedProgram`. -/

-- `SelfReduction`: `(N, e, Y) := rsa.challenge()`; `pk()` returns `(N, e)`; `challenge(i)` returns
-- `Y · r_i^e`; `check(k, X)` returns `rsa.check(X · r_i⁻¹)` for the first `i < k` with
-- `X^e = Y · r_i^e`, and false if there is none.
converter SelfReduction(bits n : ℕ) : RSAIndexed bits n
  inside rsa : RSAChallenge bits
  initialize
    rs ←$ RSA.unitTables (bits := bits) n
  on pk() → RSA.Residue bits × RSA.Residue bits
    (N, e, _Y) ← rsa.challenge()
    return (N, e)
  on challenge(i : Fin n) → RSA.Residue bits
    (N, e, Y) ← rsa.challenge()
    return RSA.mulMod N Y (RSA.powMod N e (rs i N))
  on check(k : Fin (n + 1), X : RSA.Residue bits) → Bool
    (N, e, Y) ← rsa.challenge()
    root ← (List.finRange n).find? fun i =>
      decide (i.val < k.val ∧ RSA.powMod N e X = RSA.mulMod N Y (RSA.powMod N e (rs i N)))
    match root
    | some i →
      found ← rsa.check(RSA.mulMod N X (RSA.invMod N (rs i N)))
      return found
    | none →
      return false

/-- The inside calls of `SelfReduction` per procedure: the source and `rsa.challenge()` once each,
and `rsa.check` once from `check`. -/
def SelfReduction.calls : RSAIndexed.Port → RSAChallenge.Port ⊕ Unit → ℕ
  | .check, _ => 1
  | _, .inl .check => 0
  | _, _ => 1

/-- `SelfReduction` calls each inside label at most `SelfReduction.calls` times per procedure. -/
lemma SelfReduction.labelBounded (n : ℕ) :
    (SelfReduction.body bits n).LabelBounded SelfReduction.calls := by
  intro s o u
  cases o <;> simp only [SelfReduction.body] <;> cases s <;> dsimp only <;>
    repeat' (first
      | exact Program.labelCallBound_return _ _
      | (refine Program.labelCallBound_call _ _ _ (by decide) fun y => ?_)
      | split)

/-- The inside budget of the self-reduction: `rsa.challenge()` once per query and `rsa.check` once
per check. -/
abbrev selfBudget (q : RSAIndexed.Port → ℕ) : RSAChallenge.Port → ℕ
  | .challenge => q .pk + q .challenge + q .check
  | .check => q .check

/-- The inside interface of the program of `SelfReduction`: the RSA library beside the source. -/
abbrev SelfReduction.inside (bits n : ℕ) (q : RSAIndexed.Port → ℕ) : Interface :=
  (RSAChallenge.perPort bits (selfBudget q)).tensor
    (Interface.source (lawType (SelfReduction.law1 bits n)) (SelfReduction.bound bits n * ∑ i, q i))

/-- The inside interface admits the per-label budget of `SelfReduction`. -/
lemma SelfReduction.admits (n : ℕ) (q : RSAIndexed.Port → ℕ) :
    (SelfReduction.inside bits n q).AdmitsLabelBudget
      fun j => ∑ o, SelfReduction.calls o j * q o := by
  refine ((portBudget_admitsLabelBudget _ _ _ _).tensor (queryBudget_admitsLabelBudget _ _ _
    (fun _ => ∑ i, q i) ?_)).mono fun j => ?_
  · simpa using Nat.le_mul_of_pos_left _ (by norm_num [SelfReduction.bound])
  · rcases j with (_ | _) | _ <;>
      simp [Finset.univ, Fintype.elems, SelfReduction.calls, selfBudget]
    all_goals omega

/-- **The self-reduction at per-port budgets**: the program of `SelfReduction` at the per-label
call bound `SelfReduction.calls`, beside its source. -/
def SelfReduction.perLabel (n : ℕ) (q : RSAIndexed.Port → ℕ) :
    RSAIndexed.perPort bits n q ⟶ RSAChallenge.perPort bits (selfBudget q) :=
  Converter.ofLabelBoundedProgram (A := RSAIndexed.perPort bits n q)
      (B := SelfReduction.inside bits n q) none (SelfReduction.body bits n)
      (SelfReduction.bound_spec bits n) SelfReduction.calls (SelfReduction.labelBounded n) q
      (fun _ hd => hd.2) (SelfReduction.admits n q) ≫
    Interface.rightContext _
      (SelfReduction.randomness bits n (SelfReduction.bound bits n * ∑ i, q i))

/-- The first index below `k` whose challenge `Y · r_i^e` the residue `X` is an `e`-th root of. -/
def rootIndex (key : RSA.Key bits) (Y : RSA.Residue bits) {n : ℕ}
    (rs : Fin n → RSA.Residue bits → RSA.Residue bits) (k : Fin (n + 1)) (X : RSA.Residue bits) :
    Option (Fin n) :=
  (List.finRange n).find? fun i => decide (i.val < k.val ∧
    RSA.powMod key.N key.e X = RSA.mulMod key.N Y (RSA.powMod key.N key.e (rs i key.N)))

/-- The answers of the self-reduction on the RSA library of `key`, `Y` and `chk`, with its units
`r_i`. -/
def selfAnswers (key : RSA.Key bits) (Y : RSA.Residue bits) (chk : RSA.Residue bits → Bool)
    {n : ℕ} (rs : Fin n → RSA.Residue bits → RSA.Residue bits) :
    ∀ i, (RSAIndexed bits n 0).X i → (RSAIndexed bits n 0).Y i
  | .pk => fun _ => (key.N, key.e)
  | .challenge => fun i => RSA.mulMod key.N Y (RSA.powMod key.N key.e (rs i key.N))
  | .check => fun kX => match rootIndex key Y rs kX.1 kX.2 with
    | some i => chk (RSA.mulMod key.N kX.2 (RSA.invMod key.N (rs i key.N)))
    | none => false

/-- **The self-reduction on an RSA library**: attached to the RSA library of `key`, `Y` and
`chk`, it answers with its units `r_i`. -/
lemma SelfReduction.smul_ofFunction (n : ℕ) (q : RSAIndexed.Port → ℕ) (key : RSA.Key bits)
    (Y : RSA.Residue bits) (chk : RSA.Residue bits → Bool) :
    SelfReduction.perLabel n q • Resource.ofFunction (A := RSAChallenge.perPort bits (selfBudget q))
        (RSA.library key Y chk) =
      Resource.sample (SelfReduction.law1 bits n).1 fun rs =>
        Resource.ofFunction (A := RSAIndexed.perPort bits n q) (selfAnswers key Y chk rs) := by
  unfold SelfReduction.perLabel Converter.ofLabelBoundedProgram SelfReduction.randomness
  refine ofDDC_ofProgramOn_source_smul_ofFunction (A := RSAIndexed.perPort bits n q)
    (B := RSAChallenge.perPort bits (selfBudget q)) (Z := lawType (SelfReduction.law1 bits n))
    (k := SelfReduction.bound bits n * ∑ i, q i) none (SelfReduction.body bits n)
    (SelfReduction.bound_spec bits n) _ (SelfReduction.law1 bits n) (RSA.library key Y chk) _
    (fun t c => ?_) fun h hd => Nat.mul_pos (by norm_num [SelfReduction.bound])
      (bound_pos_of_domain hd)
  have hs : ∀ u v, sourceStep (SelfReduction.law1 bits n) (t, c) u v =
      ((t, c + 1), sourceEntry (SelfReduction.law1 bits n) t c) := fun _ _ => rfl
  refine automatonSystem_of_stored _ (selfAnswers key Y chk) _ (sourceEntry _ t c)
    (fun i x => ⟨((), (t, c + 1)), ?_⟩) (fun r i x => ⟨r, ?_⟩)
  · refine Program.combine_eq_of_invoke _ _ (n := 3) ?_
    cases i <;> simp [Program.invoke, SelfReduction.body, callProg, returnProg, parallelStep, hs,
      selfAnswers, RSA.library, rootIndex]
    generalize List.find? _ (List.finRange n) = r
    cases r <;> simp [returnProg, callProg]
  · refine Program.combine_eq_of_invoke _ _ (n := 2) ?_
    cases i <;> simp [Program.invoke, SelfReduction.body, callProg, returnProg, parallelStep,
      selfAnswers, RSA.library, rootIndex]
    generalize List.find? _ (List.finRange n) = r
    cases r <;> simp [returnProg, callProg]

/-! ## The challenges of the self-reduction -/

section Challenges

variable (key : RSA.Key bits) (n : ℕ)

/-- **The challenges of the self-reduction** modulo `N`: `Y · r_i^e` for a uniform residue `Y`
and independent uniform units `r_i`. -/
def selfChallengeLaw : Distribution (Fin n → RSA.Residue bits) :=
  Distribution.fTransform (fun p : RSA.Residue bits × (Fin n → RSA.Residue bits) =>
      fun i => RSA.mulMod key.N p.1 (key.pow (p.2 i) key.e.val))
    (Distribution.prod (RSA.residue key.N).1 (Distribution.pi fun _ => (RSA.unit key.N).1))

/-- **On a unit `Y` the challenges are independent uniform units**: pointwise, the challenges of
the self-reduction are at least `φ(N)/N` times independent uniform units. -/
lemma units_le_selfChallengeLaw (hkey : ∀ x : RSA.Residue bits, x.val < key.N.val →
      key.pow (key.pow x key.e.val) key.d.val = x) (Z : Fin n → RSA.Residue bits) :
    (Nat.totient key.N.val / key.N.val : ℝ) * Distribution.pi (fun _ => (RSA.unit key.N).1) Z ≤
      selfChallengeLaw key n Z := by
  classical
  have hU : (Distribution.pi fun _ : Fin n => (RSA.unit key.N).1).NonNeg :=
    Distribution.pi_nonNeg fun _ => (RSA.unit key.N).2.1
  have hR : (RSA.residue key.N).1.NonNeg := (RSA.residue key.N).2.1
  rw [selfChallengeLaw, Distribution.fTransform_apply_eq_mass]
  refine le_of_le_of_eq ?_ (Distribution.mass_prod_eq_sum (RSA.residue key.N).1
    (Distribution.pi fun _ : Fin n => (RSA.unit key.N).1) (fun Y r =>
      (fun i => RSA.mulMod key.N Y (key.pow (r i) key.e.val)) = Z)).symm
  rw [Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  -- The units `Y` alone give `φ(N)/N` times the uniform units.
  have each : ∀ Y, RSA.IsUnit key.N Y →
      (Distribution.pi fun _ : Fin n => (RSA.unit key.N).1).mass
        (fun r => (fun i => RSA.mulMod key.N Y (key.pow (r i) key.e.val)) = Z) =
      Distribution.pi (fun _ => (RSA.unit key.N).1) Z := by
    intro Y hY
    have hmap := Distribution.fTransform_pi_map (fun _ : Fin n => (RSA.unit key.N).1)
      (fun _ r => RSA.mulMod key.N Y (key.pow r key.e.val))
    simp only [RSA.unit_mul_pow key hkey hY] at hmap
    rw [← Distribution.fTransform_apply_eq_mass, hmap]
  calc (Nat.totient key.N.val / key.N.val : ℝ) * Distribution.pi (fun _ => (RSA.unit key.N).1) Z
      = ∑ Y ∈ Finset.univ.filter (RSA.IsUnit key.N),
          (RSA.residue key.N).1 Y * Distribution.pi (fun _ => (RSA.unit key.N).1) Z := by
        rw [← Finset.sum_mul]
        congr 1
        rw [Finset.sum_congr rfl fun Y hY => by
          rw [RSA.residue_apply, if_pos (Finset.mem_filter.mp hY).2.1], Finset.sum_const,
          RSA.card_isUnit, nsmul_eq_mul]
        ring
    _ ≤ ∑ Y ∈ Finset.univ.filter (RSA.IsUnit key.N), (RSA.residue key.N).1 Y *
          (Distribution.pi fun _ : Fin n => (RSA.unit key.N).1).mass
            (fun r => (fun i => RSA.mulMod key.N Y (key.pow (r i) key.e.val)) = Z) :=
        le_of_eq (Finset.sum_congr rfl fun Y hY => by rw [each Y (Finset.mem_filter.mp hY).2])
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun Y _ _ =>
        mul_nonneg (hR Y) (hU.mass_nonneg _)

/-- **The challenges of `rsa*` and of the self-reduction modulo `N` are close**: for every
`l ≥ 0`, in `ℓ¹` independent uniform residues are within `|c^n - l c| + (1 - c^n) + l (1 - c)` of
`l` times the challenges of the self-reduction, `c = φ(N)/N` the probability of a unit. -/
lemma sum_abs_residues_sub_selfChallengeLaw_le (hkey : ∀ x : RSA.Residue bits,
      x.val < key.N.val → key.pow (key.pow x key.e.val) key.d.val = x) {l : ℝ} (hl : 0 ≤ l) :
    ∑ Z, |Distribution.pi (fun _ : Fin n => (RSA.residue key.N).1) Z -
        l * selfChallengeLaw key n Z| ≤
      |(Nat.totient key.N.val / key.N.val : ℝ) ^ n - l * (Nat.totient key.N.val / key.N.val)| +
        (1 - (Nat.totient key.N.val / key.N.val : ℝ) ^ n) +
        l * (1 - Nat.totient key.N.val / key.N.val) := by
  set c : ℝ := Nat.totient key.N.val / key.N.val
  set U := Distribution.pi fun _ : Fin n => (RSA.unit key.N).1
  set A := Distribution.pi fun _ : Fin n => (RSA.residue key.N).1
  set ρ := selfChallengeLaw key n
  have hU : U.isProbDist := Distribution.pi_isProbDist fun _ => (RSA.unit key.N).2
  have hA : A.isProbDist := Distribution.pi_isProbDist fun _ => (RSA.residue key.N).2
  have hρ : ρ.isProbDist := Distribution.fTransform_isProbDist _
    (Distribution.prod_isProbDist _ _ (RSA.residue key.N).2 hU)
  have hAU := RSA.units_le_residues key n
  have hρU := units_le_selfChallengeLaw key n hkey
  calc ∑ Z, |A Z - l * ρ Z|
      ≤ ∑ Z, (|c ^ n - l * c| * U Z + (A Z - c ^ n * U Z) + l * (ρ Z - c * U Z)) := by
        refine Finset.sum_le_sum fun Z _ => ?_
        have e : A Z - l * ρ Z = (c ^ n - l * c) * U Z + (A Z - c ^ n * U Z) -
            l * (ρ Z - c * U Z) := by ring
        rw [e]
        refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
        · rw [abs_mul, abs_of_nonneg (hU.1 Z)]
        · exact (abs_of_nonneg (sub_nonneg.mpr (hAU Z))).le
        · rw [abs_mul, abs_of_nonneg hl, abs_of_nonneg (sub_nonneg.mpr (hρU Z))]
    _ = |c ^ n - l * c| + (1 - c ^ n) + l * (1 - c) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Distribution.sum_eq_one U hU, Distribution.sum_eq_one A hA, Distribution.sum_eq_one ρ hρ]
        ring

end Challenges

/-- **The loss of the self-reduction**: for a unit probability `c = 1 - ν ≥ 1 - δ` and
`(n + 1) δ < 1`, the bound of `sum_abs_residues_sub_selfChallengeLaw_le` at `l = (1 - δ)^(n-1)` is
at most `(n + 1) δ`. -/
lemma selfReduction_loss_le {n : ℕ} (hn : 1 ≤ n) {ν δ : ℝ} (hν : 0 ≤ ν) (hνδ : ν ≤ δ)
    (hδ : (n + 1) * δ < 1) :
    |(1 - ν) ^ n - (1 - δ) ^ (n - 1) * (1 - ν)| + (1 - (1 - ν) ^ n) +
      (1 - δ) ^ (n - 1) * (1 - (1 - ν)) ≤ (n + 1) * δ := by
  have hδ0 : 0 ≤ δ := hν.trans hνδ
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ1 : δ ≤ 1 / 2 := by nlinarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hle : (1 - δ) ^ m ≤ (1 - ν) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
  have hpos : 0 ≤ (1 - ν) ^ (m + 1) - (1 - δ) ^ m * (1 - ν) := by
    rw [pow_succ]; nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 - δ by linarith) m]
  rw [abs_of_nonneg hpos]
  have hb : 1 - m * δ ≤ (1 - δ) ^ m := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -δ by linarith) m
    simpa [sub_eq_add_neg, mul_neg] using this
  push_cast at hδ ⊢
  have hl0 : (0 : ℝ) ≤ (1 - δ) ^ m := pow_nonneg (by linarith) m
  nlinarith [mul_nonneg (sub_nonneg.mpr hb) (show (0 : ℝ) ≤ 1 - 2 * δ by linarith),
    mul_nonneg hl0 (sub_nonneg.mpr hνδ), mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
      (mul_nonneg hδ0 hδ0)]

/-! ## The self-reduction on sampled functions -/

/-- The challenges `Y · r_i^e` of the self-reduction, for its units `r_i`. -/
def selfChallenge (key : RSA.Key bits) (Y : RSA.Residue bits) {n : ℕ}
    (rs : Fin n → RSA.Residue bits → RSA.Residue bits) : Fin n → RSA.Residue bits :=
  fun i => RSA.mulMod key.N Y (key.pow (rs i key.N) key.e.val)

/-- The answers of the indexed `rsa*-real` on the key and the challenges `Z`. -/
def indexedReal {n : ℕ} (kZ : RSA.Key bits × (Fin n → RSA.Residue bits)) :
    ∀ i, (RSAIndexed bits n 0).X i → (RSAIndexed bits n 0).Y i
  | .pk => fun _ => (kZ.1.N, kZ.1.e)
  | .challenge => fun i => kZ.2 i
  | .check => fun kX =>
    decide (∃ i : Fin n, i.val < kX.1.val ∧ kZ.1.pow kX.2 kZ.1.e.val = kZ.2 i)

/-- The answers of the indexed `rsa*-fake` on the key and the challenges `Z`. -/
def indexedFake {n : ℕ} (kZ : RSA.Key bits × (Fin n → RSA.Residue bits)) :
    ∀ i, (RSAIndexed bits n 0).X i → (RSAIndexed bits n 0).Y i
  | .pk => fun _ => (kZ.1.N, kZ.1.e)
  | .challenge => fun i => kZ.2 i
  | .check => fun _ => false

/-- **The self-reduction on `rsa-real` answers as `rsa*-real`** on its challenges, for a residue
`Y` modulo `N` and units `r_i`: a root of the `i`-th challenge gives a root of `Y`. -/
lemma selfAnswers_real (key : RSA.Key bits) {Y : RSA.Residue bits} (hY : Y.val < key.N.val)
    {n : ℕ} {rs : Fin n → RSA.Residue bits → RSA.Residue bits}
    (hrs : ∀ i, RSA.IsUnit key.N (rs i key.N)) :
    selfAnswers key Y (fun X => decide (Y = key.pow X key.e.val)) rs =
      indexedReal (key, selfChallenge key Y rs) := by
  funext o x
  cases o
  · rfl
  · simp [selfAnswers, indexedReal, selfChallenge, RSA.powMod_eq_pow]
  · obtain ⟨k, X⟩ := x
    simp only [selfAnswers, indexedReal, selfChallenge]
    cases h : rootIndex key Y rs k X with
    | some i =>
      unfold rootIndex at h
      have hp := List.find?_some h
      simp only [decide_eq_true_eq] at hp
      obtain ⟨hik, hX⟩ := hp
      rw [RSA.powMod_eq_pow, RSA.powMod_eq_pow] at hX
      exact decide_eq_decide.mpr ⟨fun _ => ⟨i, hik, hX⟩,
        fun _ => (RSA.pow_mulMod_invMod key hY (hrs i) hX).symm⟩
    | none =>
      unfold rootIndex at h
      refine (decide_eq_false fun ⟨i, hik, hX⟩ => ?_).symm
      have hi := List.find?_eq_none.mp h i (List.mem_finRange i)
      simp only [RSA.powMod_eq_pow, decide_eq_true_eq] at hi
      exact hi ⟨hik, hX⟩

/-- **The self-reduction on `rsa-fake` answers as `rsa*-fake`** on its challenges. -/
lemma selfAnswers_fake (key : RSA.Key bits) (Y : RSA.Residue bits) {n : ℕ}
    (rs : Fin n → RSA.Residue bits → RSA.Residue bits) :
    selfAnswers key Y (fun _ => false) rs = indexedFake (key, selfChallenge key Y rs) := by
  funext o x
  cases o
  · rfl
  · simp [selfAnswers, indexedFake, selfChallenge, RSA.powMod_eq_pow]
  · simp only [selfAnswers, indexedFake]
    split <;> rfl

/-- **The key and the challenges of `rsa*`**: a generated key and independent uniform residues
modulo its `N`. -/
def starLaw (keyGen : Distribution.ProbDist (RSA.Key bits)) (n : ℕ) :
    Distribution (RSA.Key bits × (Fin n → RSA.Residue bits)) :=
  Distribution.fTransform (fun kY => (kY.1, fun i => kY.2 i kY.1.N))
    (Distribution.prod keyGen.1
      (Distribution.ProbDist.pi fun _ : Fin n => RSA.residues (bits := bits)).1)

/-- **The key and the challenges of the self-reduction**: a generated key and `Y · r_i^e` for a
uniform residue `Y` and independent uniform units `r_i` modulo its `N`. -/
def selfLaw (keyGen : Distribution.ProbDist (RSA.Key bits)) (n : ℕ) :
    Distribution (RSA.Key bits × (Fin n → RSA.Residue bits)) :=
  Distribution.fTransform (fun p : RSA.Key bits × (RSA.Residue bits → RSA.Residue bits) ×
      (Fin n → RSA.Residue bits → RSA.Residue bits) =>
        (p.1, selfChallenge p.1 (p.2.1 p.1.N) p.2.2))
    (Distribution.prod keyGen.1
      (Distribution.prod (RSA.residues (bits := bits)).1 (RSA.unitTables (bits := bits) n).1))

instance starLaw.isProbability (keyGen : Distribution.ProbDist (RSA.Key bits)) (n : ℕ) :
    Distribution.IsProbability (starLaw keyGen n) := by
  unfold starLaw; infer_instance

instance selfLaw.isProbability (keyGen : Distribution.ProbDist (RSA.Key bits)) (n : ℕ) :
    Distribution.IsProbability (selfLaw keyGen n) := by
  unfold selfLaw; infer_instance

/-- **The key and the challenges of `rsa*`**, at a key: the key's probability times independent
uniform residues. -/
lemma starLaw_apply (keyGen : Distribution.ProbDist (RSA.Key bits)) (n : ℕ) (key : RSA.Key bits)
    (Z : Fin n → RSA.Residue bits) :
    starLaw keyGen n (key, Z) =
      keyGen.1 key * Distribution.pi (fun _ : Fin n => (RSA.residue key.N).1) Z := by
  refine (Distribution.fTransform_prod_fiber_apply keyGen.1 _
    (fun (key : RSA.Key bits) (Ys : Fin n → RSA.Residue bits → RSA.Residue bits) (i : Fin n) =>
      Ys i key.N) key Z).trans ?_
  congr 1
  refine (DFunLike.congr_fun (Distribution.fTransform_pi_map
    (fun _ : Fin n => (RSA.residues (bits := bits)).1) fun _ Ys => Ys key.N) Z).trans ?_
  congr 2
  funext i
  exact RSA.fTransform_eval_residues key.N

/-- **The key and the challenges of the self-reduction**, at a key: the key's probability times
the challenges of the self-reduction modulo its `N`. -/
lemma selfLaw_apply (keyGen : Distribution.ProbDist (RSA.Key bits)) (n : ℕ) (key : RSA.Key bits)
    (Z : Fin n → RSA.Residue bits) :
    selfLaw keyGen n (key, Z) = keyGen.1 key * selfChallengeLaw key n Z := by
  refine (Distribution.fTransform_prod_fiber_apply keyGen.1 _
    (fun (key : RSA.Key bits) (p : (RSA.Residue bits → RSA.Residue bits) ×
      (Fin n → RSA.Residue bits → RSA.Residue bits)) => selfChallenge key (p.1 key.N) p.2)
    key Z).trans ?_
  congr 1
  have hcomp : (fun p : (RSA.Residue bits → RSA.Residue bits) ×
      (Fin n → RSA.Residue bits → RSA.Residue bits) => selfChallenge key (p.1 key.N) p.2) =
      (fun p : RSA.Residue bits × (Fin n → RSA.Residue bits) =>
        fun i => RSA.mulMod key.N p.1 (key.pow (p.2 i) key.e.val)) ∘
        Prod.map (fun Ys => Ys key.N) fun rs i => rs i key.N := rfl
  rw [hcomp, ← Distribution.fTransform_comp, Distribution.fTransform_prod,
    RSA.fTransform_eval_residues, RSA.fTransform_eval_unitTables]
  rfl

/-- **The indexed `rsa*-real` samples its answers** on the key and the challenges of `rsa*`. -/
lemma Indexed.real_eq_sample (keyGen : Distribution.ProbDist (RSA.Key bits)) (n : ℕ)
    (q : RSAIndexed.Port → ℕ) :
    RSAStar.Indexed.real keyGen n (q := q) = Resource.sample (starLaw keyGen n) fun kZ =>
      Resource.ofFunction (A := RSAIndexed.perPort bits n q) (indexedReal kZ) := by
  unfold RSAStar.Indexed.real
  refine Resource.sample_eq_sample_of_fTransform _ _ (fun kY => (kY.1, fun i => kY.2 i kY.1.N))
    _ _ rfl fun kY => ?_
  congr 1
  funext i
  cases i <;> rfl

/-- **The indexed `rsa*-fake` samples its answers** on the key and the challenges of `rsa*`. -/
lemma Indexed.fake_eq_sample (keyGen : Distribution.ProbDist (RSA.Key bits)) (n : ℕ)
    (q : RSAIndexed.Port → ℕ) :
    RSAStar.Indexed.fake keyGen n (q := q) = Resource.sample (starLaw keyGen n) fun kZ =>
      Resource.ofFunction (A := RSAIndexed.perPort bits n q) (indexedFake kZ) := by
  unfold RSAStar.Indexed.fake
  refine Resource.sample_eq_sample_of_fTransform _ _ (fun kY => (kY.1, fun i => kY.2 i kY.1.N))
    _ _ rfl fun kY => ?_
  congr 1
  funext i
  cases i <;> rfl

/-- **The self-reduction on `rsa-real`** is the indexed `rsa*-real` on its challenges. -/
lemma SelfReduction.smul_real (keyGen : Distribution.ProbDist (RSA.Key bits)) (n : ℕ)
    (q : RSAIndexed.Port → ℕ) :
    SelfReduction.perLabel n q • RSA.Real.perPort keyGen =
      Resource.sample (selfLaw keyGen n) fun kZ =>
        Resource.ofFunction (A := RSAIndexed.perPort bits n q) (indexedReal kZ) := by
  rw [RSA.Real.perPort_eq_sampled, RSA.Real.sampled_eq_library, Resource.smul_sample]
  simp only [SelfReduction.smul_ofFunction]
  rw [Resource.sample_sample]
  refine Resource.sample_eq_sample_of_fTransform_support _ _
    (fun x => (x.1.1, selfChallenge x.1.1 (x.1.2 x.1.1.N) x.2)) _ _
    (Distribution.fTransform_prod_assoc _ _ _ _) fun x hx => ?_
  obtain ⟨⟨key, Ys⟩, rs⟩ := x
  have hmem := Finset.mem_product.mp (Distribution.support_prod_subset _ _ hx)
  have hY := Finset.mem_product.mp (Distribution.support_prod_subset _ _ hmem.1)
  dsimp only
  rw [selfAnswers_real key (RSA.lt_of_mem_support_residue key.2
    (Distribution.ProbDist.mem_support_pi hY.2 key.N)) fun i => RSA.isUnit_of_mem_support_unit key
      (Distribution.ProbDist.mem_support_pi (Distribution.ProbDist.mem_support_pi hmem.2 i) key.N)]

/-- **The self-reduction on `rsa-fake`** is the indexed `rsa*-fake` on its challenges. -/
lemma SelfReduction.smul_fake (keyGen : Distribution.ProbDist (RSA.Key bits)) (n : ℕ)
    (q : RSAIndexed.Port → ℕ) :
    SelfReduction.perLabel n q • RSA.Fake.perPort keyGen =
      Resource.sample (selfLaw keyGen n) fun kZ =>
        Resource.ofFunction (A := RSAIndexed.perPort bits n q) (indexedFake kZ) := by
  rw [RSA.Fake.perPort_eq_sampled, RSA.Fake.sampled_eq_library, Resource.smul_sample]
  simp only [SelfReduction.smul_ofFunction]
  rw [Resource.sample_sample]
  refine Resource.sample_eq_sample_of_fTransform _ _
    (fun x => (x.1.1, selfChallenge x.1.1 (x.1.2 x.1.1.N) x.2)) _ _
    (Distribution.fTransform_prod_assoc _ _ _ _) fun x => ?_
  rw [selfAnswers_fake]

/-- **The self-reduction between the RSA libraries**: if `rsa-real` substitutes for `rsa-fake`
within `ε`, the indexed `rsa*-real` substitutes for the indexed `rsa*-fake` on the challenges of
the self-reduction within `ε` at the reduced distinguisher. -/
lemma SelfReduction.substitutesWithin [AdmissibleDistinguishers]
    (keyGen : Distribution.ProbDist (RSA.Key bits)) (n : ℕ) (q : RSAIndexed.Port → ℕ)
    {ε : (RSAChallenge.perPort bits (selfBudget q)).inputDomain.DistinguisherBehavior → ENNReal}
    (secure : RSA.Assumption keyGen ε) :
    Resource.sample (selfLaw keyGen n) (fun kZ =>
        Resource.ofFunction (A := RSAIndexed.perPort bits n q) (indexedReal kZ)) ≃[ε ∘ absorb
          (SelfReduction.perLabel n q)]
      Resource.sample (selfLaw keyGen n) fun kZ =>
        Resource.ofFunction (A := RSAIndexed.perPort bits n q) (indexedFake kZ) := by
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    Resource.sample (selfLaw keyGen n) (fun kZ =>
        Resource.ofFunction (A := RSAIndexed.perPort bits n q) (indexedReal kZ)) =
        SelfReduction.perLabel n q • RSA.Real.perPort keyGen :=
      (SelfReduction.smul_real keyGen n q).symm
    _ ≃[ε ∘ absorb (SelfReduction.perLabel n q)]
        SelfReduction.perLabel n q • (RSA.Reject.perPort bits • RSA.Real.perPort keyGen) :=
      AdmissibleDistinguishers.substitutesWithin_context _ secure
    _ = SelfReduction.perLabel n q • RSA.Fake.perPort keyGen := by
      rw [RSA.Fake.perPort_eq_reject]
    _ = Resource.sample (selfLaw keyGen n) fun kZ =>
        Resource.ofFunction (A := RSAIndexed.perPort bits n q) (indexedFake kZ) :=
      SelfReduction.smul_fake keyGen n q

/-- **The challenges of `rsa*` and of the self-reduction are close**: in `ℓ¹`, the key and the
challenges of `rsa*` are within `(n + 1) δ` of `λ` times those of the self-reduction, for some
`λ ∈ [0, 1]`. -/
theorem sum_abs_starLaw_sub_selfLaw_le (keyGen : Distribution.ProbDist (RSA.Key bits))
    (correct : RSA.Correct keyGen) (δ : ℝ) (nonUnit : RSA.NonUnitBound keyGen δ) (n : ℕ) :
    ∃ l : ℝ, 0 ≤ l ∧ l ≤ 1 ∧
      ∑ kZ, |starLaw keyGen n kZ - l * selfLaw keyGen n kZ| ≤ (n + 1) * δ := by
  have hstar : (starLaw keyGen n).isProbDist := Distribution.fTransform_isProbDist _
    (Distribution.prod_isProbDist _ _ keyGen.2 (Distribution.ProbDist.pi _).2)
  -- At `(n + 1) δ ≥ 1`, the bound holds at `λ = 0`.
  by_cases hδ : 1 ≤ (n + 1) * δ
  · refine ⟨0, le_rfl, zero_le_one, ?_⟩
    simp only [zero_mul, sub_zero]
    rw [Finset.sum_congr rfl fun kZ _ => abs_of_nonneg (hstar.1 kZ),
      Distribution.sum_eq_one _ hstar]
    exact hδ
  replace hδ := not_le.mp hδ
  obtain ⟨key₀, hkey₀⟩ : keyGen.1.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h
    have hw := keyGen.2.2
    rw [h] at hw
    simp [Distribution.weight] at hw
  have hν : ∀ key : RSA.Key bits,
      0 ≤ ((key.N.val : ℝ) - Nat.totient key.N.val) / key.N.val := fun key =>
    div_nonneg (sub_nonneg.mpr (by exact_mod_cast Nat.totient_le _)) (Nat.cast_nonneg _)
  have hδ₀ : 0 ≤ δ := (hν key₀).trans (nonUnit key₀ hkey₀)
  have hδ₁ : δ ≤ 1 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  -- Otherwise at `λ = (1 - δ)^(n-1)`, key by key.
  have perKey : ∀ key ∈ keyGen.1.support, ∑ Z, |Distribution.pi (fun _ : Fin n =>
      (RSA.residue key.N).1) Z - (1 - δ) ^ (n - 1) * selfChallengeLaw key n Z| ≤
        (n + 1) * δ := by
    intro key hk
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hA := Distribution.sum_eq_one _
        (Distribution.pi_isProbDist fun _ : Fin 0 => (RSA.residue key.N).2)
      have hρ := Distribution.sum_eq_one (selfChallengeLaw key 0)
        (Distribution.fTransform_isProbDist _ (Distribution.prod_isProbDist _ _
          (RSA.residue key.N).2 (Distribution.pi_isProbDist fun _ => (RSA.unit key.N).2)))
      rw [Fintype.sum_unique] at hA hρ ⊢
      rw [hA, hρ]
      simpa using hδ₀
    · have hN : (0 : ℝ) < key.N.val := by exact_mod_cast key.2
      have hb := sum_abs_residues_sub_selfChallengeLaw_le key n (correct key hk)
        (l := (1 - δ) ^ (n - 1)) (pow_nonneg (by linarith) _)
      rw [show (Nat.totient key.N.val / key.N.val : ℝ) =
          1 - ((key.N.val : ℝ) - Nat.totient key.N.val) / key.N.val by
        rw [sub_div, div_self hN.ne', sub_sub_cancel]] at hb
      exact hb.trans (selfReduction_loss_le hn (hν key) (nonUnit key hk) hδ)
  refine ⟨(1 - δ) ^ (n - 1), pow_nonneg (by linarith) _, pow_le_one₀ (by linarith) (by linarith),
    ?_⟩
  rw [Fintype.sum_prod_type]
  calc ∑ key, ∑ Z, |starLaw keyGen n (key, Z) - (1 - δ) ^ (n - 1) * selfLaw keyGen n (key, Z)|
      = ∑ key, keyGen.1 key * ∑ Z, |Distribution.pi (fun _ : Fin n => (RSA.residue key.N).1) Z -
          (1 - δ) ^ (n - 1) * selfChallengeLaw key n Z| := by
        refine Finset.sum_congr rfl fun key _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun Z _ => ?_
        rw [starLaw_apply, selfLaw_apply, ← abs_of_nonneg (keyGen.2.1 key), ← abs_mul,
          abs_of_nonneg (keyGen.2.1 key)]
        congr 1
        ring
    _ ≤ ∑ key, keyGen.1 key * ((n + 1) * δ) := Finset.sum_le_sum fun key _ => by
        by_cases hk : key ∈ keyGen.1.support
        · exact mul_le_mul_of_nonneg_left (perKey key hk) (keyGen.2.1 key)
        · rw [Finsupp.notMem_support_iff.mp hk, zero_mul, zero_mul]
    _ = (n + 1) * δ := by rw [← Finset.sum_mul, Distribution.sum_eq_one _ keyGen.2, one_mul]

/-- **Random self-reduction** [1, §8.1], with indexed challenges: if the RSA assumption holds
within `ε`, the indexed many-challenge assumption for `n` challenges holds within `ε` at the
reduced distinguisher and `δ` per challenge and for the challenge of the assumption. -/
theorem rsa_self_reduction_indexed [AdmissibleDistinguishers]
    (keyGen : Distribution.ProbDist (RSA.Key bits)) (correct : RSA.Correct keyGen) (δ : ℝ)
    (nonUnit : RSA.NonUnitBound keyGen δ) (n : ℕ) (q : RSAIndexed.Port → ℕ) :
    ∀ ε, RSA.Assumption keyGen ε →
      RSAStar.Indexed keyGen fun D =>
        ε (absorb (SelfReduction.perLabel n q) D) + ENNReal.ofReal (((n : ℝ) + 1) * δ) := by
  intro ε secure
  obtain ⟨l, hl₀, hl₁, close⟩ := sum_abs_starLaw_sub_selfLaw_le keyGen correct δ nonUnit n
  show RSAStar.Indexed.real keyGen n ≃[_]
    RSAStar.Indexed.Reject.perPort bits n • RSAStar.Indexed.real keyGen n
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    RSAStar.Indexed.real keyGen n = Resource.sample (starLaw keyGen n) fun kZ =>
        Resource.ofFunction (A := RSAIndexed.perPort bits n q) (indexedReal kZ) :=
      Indexed.real_eq_sample keyGen n q
    _ ≃[fun D => ε (absorb (SelfReduction.perLabel n q) D) + ENNReal.ofReal (((n : ℝ) + 1) * δ)]
        Resource.sample (starLaw keyGen n) fun kZ =>
          Resource.ofFunction (A := RSAIndexed.perPort bits n q) (indexedFake kZ) :=
      Resource.substitutesWithin_sample _ _ _ _ hl₀ hl₁ close
        (SelfReduction.substitutesWithin keyGen n q secure)
    _ = RSAStar.Indexed.fake keyGen n := (Indexed.fake_eq_sample keyGen n q).symm
    _ = RSAStar.Indexed.Reject.perPort bits n • RSAStar.Indexed.real keyGen n :=
      RSAStar.Indexed.fake_eq_reject keyGen n q

/-- **The random self-reduction for `rsa*`**: the challenges counted, then the self-reduction
on the indexed challenges. -/
def RSAStar.selfReduction (q : RSAStar.Port → ℕ) :
    RSAStar.perPort bits q ⟶ RSAChallenge.perPort bits (fun
      | .challenge => q .pk + q .challenge + q .check
      | .check => q .check) :=
  RSAStar.Count.perPort bits (q .challenge) ≫
    SelfReduction.perLabel (q .challenge) (RSAStar.Count.insideBudget bits (q .challenge) q)

/-- **Random self-reduction** [1, §8.1]: if the RSA assumption holds within `ε`, then its
many-challenge form holds within `ε` at the distinguisher with `RSAStar.selfReduction` absorbed
and `δ` per challenge and for the challenge of the assumption. The reduction calls
`rsa.challenge()` once per query and `rsa.check` once per check. -/
theorem rsa_self_reduction [AdmissibleDistinguishers]
    (keyGen : Distribution.ProbDist (RSA.Key bits)) (correct : RSA.Correct keyGen) (δ : ℝ)
    (nonUnit : RSA.NonUnitBound keyGen δ) (q : RSAStar.Port → ℕ) :
    ∀ ε, RSA.Assumption keyGen ε →
      RSAStar.Assumption keyGen fun D =>
        ε (absorb (RSAStar.selfReduction q) D) + ENNReal.ofReal (((q .challenge : ℝ) + 1) * δ) := by
  intro ε secure
  have indexed := rsa_self_reduction_indexed keyGen correct δ nonUnit (q .challenge)
    (RSAStar.Count.insideBudget bits (q .challenge) q) ε secure
  show RSAStar.Real.perPort keyGen ≃[_] RSAStar.Reject.perPort bits • RSAStar.Real.perPort keyGen
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    RSAStar.Real.perPort keyGen =
        RSAStar.Count.perPort bits (q .challenge) • RSAStar.Indexed.real keyGen (q .challenge) :=
      RSAStar.Real.perPort_eq_count keyGen q
    _ ≃[fun D => ε (absorb (RSAStar.selfReduction q) D) +
          ENNReal.ofReal (((q .challenge : ℝ) + 1) * δ)]
        RSAStar.Count.perPort bits (q .challenge) • (RSAStar.Indexed.Reject.perPort bits
          (q .challenge) • RSAStar.Indexed.real keyGen (q .challenge)) :=
      ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.mono _
        (AdmissibleDistinguishers.substitutesWithin_context _ indexed) fun D _ =>
          le_of_eq (congrArg (fun E => ε E + _) (absorb_comp _ _ D).symm)
    _ = RSAStar.Fake.perPort keyGen := by
      rw [← RSAStar.Indexed.fake_eq_reject, RSAStar.Fake.perPort_eq_count]
    _ = RSAStar.Reject.perPort bits • RSAStar.Real.perPort keyGen :=
      RSAStar.Fake.perPort_eq_reject keyGen q

/-! ## The reduction to the many-challenge assumption

The reduction `𝓡` programs the oracle: it keeps the table `H` of the points of the oracle defined
so far, each with its value `Y` and, for a point programmed at a signature query, its root `S`. It
calls `rsa*.pk()` once per query, `rsa*.challenge()` once per oracle or verification query at a
new point and `rsa*.check` once per verification query at a challenge point, beside its sources
of `R` and `S`: its program is bounded per label, `Converter.ofLabelBoundedProgram`. -/

-- `𝓡`: `(N, e) := rsa*.pk()` on every query; `pk()` returns `(N, e)`; `sign(m)` samples
-- `R ← Salt` and `S ← ℤ_N`, and at a new point `m ‖ R` programs `RO(m ‖ R) := S^e` and returns
-- `(R, S)`, at a point it programmed returns its root, and fails at a challenge point; `ro(m, R)`
-- returns `RO(m ‖ R)`, answering a new point with `rsa*.challenge()`; `ver(m, (R, S))` returns
-- `RO(m ‖ R) = S^e mod N` at a programmed point, and at a challenge point `Y` asks
-- `rsa*.check(S)` when `S` is a residue with `S^e mod N = Y`.
converter 𝓡(bits : ℕ) (Salt : Type) [Fintype Salt] [Nonempty Salt] [DecidableEq Salt] (M : Type) [Fintype M] [DecidableEq M] : SigningRO (RSA.Residue bits × RSA.Residue bits) M (Salt × RSA.Residue bits) (M × Salt) (RSA.Residue bits)
  inside rsa : RSAStar bits
  initialize
    H ← ([] : List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits)))
  on pk() → RSA.Residue bits × RSA.Residue bits
    (N, e) ← rsa.pk()
    return (N, e)
  on sign(m : M) → Salt × RSA.Residue bits
    (N, e) ← rsa.pk()
    R ←$ 𝒰[Salt]
    Ss ←$ RSA.residues (bits := bits)
    match H.lookup (m, R)
    | some (_Y, some S) →
      return (R, S)
    | some (_Y, none) →
      return (R, Ss N)
    | none →
      H ← H ++ [((m, R), RSA.powMod N e (Ss N), some (Ss N))]
      return (R, Ss N)
  on ver(m : M, R : Salt, S : RSA.Residue bits) → Bool
    (N, e) ← rsa.pk()
    match H.lookup (m, R)
    | some (Y, some _S₀) →
      return decide (S.val < N.val ∧ Y = RSA.powMod N e S)
    | some (Y, none) →
      if S.val < N.val ∧ Y = RSA.powMod N e S
        found ← rsa.check(S)
        return found
      else
        return false
    | none →
      Y ← rsa.challenge()
      H ← H ++ [((m, R), Y, none)]
      if S.val < N.val ∧ Y = RSA.powMod N e S
        found ← rsa.check(S)
        return found
      else
        return false
  on ro(m : M, R : Salt) → RSA.Residue bits
    (_N, _e) ← rsa.pk()
    match H.lookup (m, R)
    | some (Y, _r) →
      return Y
    | none →
      Y ← rsa.challenge()
      H ← H ++ [((m, R), Y, none)]
      return Y

/-- The inside calls of `𝓡` per procedure: `rsa*.pk()` and the sources once each,
`rsa*.challenge()` once from `ver` and `ro`, and `rsa*.check` once from `ver`. -/
def 𝓡.calls : SigningRO.Port → RSAStar.Port ⊕ (Unit ⊕ Unit) → ℕ
  | .ver, .inl .check => 1
  | _, .inl .check => 0
  | .ver, .inl .challenge => 1
  | .ro, .inl .challenge => 1
  | _, .inl .challenge => 0
  | _, _ => 1

/-- `𝓡` calls each inside label at most `𝓡.calls` times per procedure. -/
lemma 𝓡.labelBounded (Salt : Type) [Fintype Salt] [Nonempty Salt] [DecidableEq Salt]
    (M : Type) [Fintype M] [DecidableEq M] :
    (𝓡.body bits Salt M).LabelBounded 𝓡.calls := by
  intro s o u
  cases o <;> simp only [𝓡.body] <;> cases s <;> dsimp only <;>
    repeat' (first
      | exact Program.labelCallBound_return _ _
      | (refine Program.labelCallBound_call _ _ _ (by decide) fun y => ?_)
      | split)

/-- The inside budget of the reduction: `rsa*.pk()` once per query, `rsa*.challenge()` once per
oracle and verification query, and `rsa*.check` once per verification query. -/
abbrev insideBudget (q : SigningRO.Port → ℕ) : RSAStar.Port → ℕ
  | .pk => q .pk + q .sign + q .ver + q .ro
  | .challenge => q .ver + q .ro
  | .check => q .ver

/-- The inside interface of the program of `𝓡`: the many-challenge library beside the sources. -/
abbrev 𝓡.inside (bits : ℕ) (Salt : Type) [Fintype Salt] [Nonempty Salt] [DecidableEq Salt]
    (M : Type) [Fintype M] [DecidableEq M] (q : SigningRO.Port → ℕ) :
    Interface :=
  (RSAStar.perPort bits (insideBudget q)).tensor
    ((Interface.source (lawType (𝓡.law1 bits Salt M)) (𝓡.bound bits Salt M * ∑ i, q i)).tensor
      (Interface.source (lawType (𝓡.law2 bits Salt M)) (𝓡.bound bits Salt M * ∑ i, q i)))

/-- The inside interface admits the per-label budget of `𝓡`. -/
lemma 𝓡.admits (Salt : Type) [Fintype Salt] [Nonempty Salt] [DecidableEq Salt]
    (M : Type) [Fintype M] [DecidableEq M] (q : SigningRO.Port → ℕ) :
    (𝓡.inside bits Salt M q).AdmitsLabelBudget fun j => ∑ o, 𝓡.calls o j * q o := by
  have hs : ∑ i, q i ≤ 𝓡.bound bits Salt M * ∑ i, q i :=
    Nat.le_mul_of_pos_left _ (by norm_num [𝓡.bound])
  refine ((portBudget_admitsLabelBudget _ _ _ _).tensor
    ((queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simpa using hs)).tensor
      (queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simpa using hs)))).mono
    fun j => ?_
  · rcases j with (_ | _ | _) | (_ | _) <;>
      simp [Finset.univ, Fintype.elems, 𝓡.calls, insideBudget]
    all_goals omega

/-- **The reduction at per-port budgets**: the program of `𝓡` at the per-label call bound
`𝓡.calls`, beside its sources. -/
def 𝓡.perLabel (Salt : Type) [Fintype Salt] [Nonempty Salt] [DecidableEq Salt]
    (M : Type) [Fintype M] [DecidableEq M] (q : SigningRO.Port → ℕ) :
    SigRO.perPort bits Salt M q ⟶ RSAStar.perPort bits (insideBudget q) :=
  Converter.ofLabelBoundedProgram (A := SigRO.perPort bits Salt M q)
      (B := 𝓡.inside bits Salt M q) none (𝓡.body bits Salt M) (𝓡.bound_spec bits Salt M)
      𝓡.calls (𝓡.labelBounded Salt M) q (fun _ hd => hd.2) (𝓡.admits Salt M q) ≫
    Interface.rightContext _
      (𝓡.randomness bits Salt M (𝓡.bound bits Salt M * ∑ i, q i))

/-! ## The proof of RSA-PSS

The four libraries of the chain are presented as one automaton with the oracle sampled lazily,
`Lazy.step sign verify`, which keeps the table `H` of the oracle, the signatures `𝒮` issued and a
flag for bad, and differs only in its signing and verification rules. `sig-real+ro` and
`sig-fake` are it along the kernel that fills the rest of the oracle with uniform residues;
`𝓡` on `rsa*-real` and on `rsa*-fake` are it along a map of states. The reduction and the
libraries step alike until a signature query hits a point of the oracle without a root. -/

/-! ### Upstream candidates

`Probability.Distribution.mass_bindK`, for `Probability.Distribution` beside `bindK`, and
`List.lookup_append_of_lookup_eq_none`, for Mathlib's `Mathlib.Data.List`. -/

section Upstream

open Probability.Distribution

/-- The mass of an event under a mixture. -/
lemma _root_.Probability.Distribution.mass_bindK {A B : Type} (μ : Distribution A)
    (f : A → Distribution B) (P : B → Prop) :
    (bindK μ f).mass P = μ.sum fun a w => w * (f a).mass P := by
  rw [← weight_restrict, restrict_bindK, weight_bindK]
  simp only [weight_restrict]

/-- **Appending a new key** to an association list: the lookup at it is its value, and elsewhere
it is unchanged. -/
lemma _root_.List.lookup_append_of_lookup_eq_none {α β : Type} [BEq α] [LawfulBEq α]
    [DecidableEq α] {l : List (α × β)} {p : α} (hp : l.lookup p = none) (v : β) (p' : α) :
    (l ++ [(p, v)]).lookup p' = if p' = p then some v else l.lookup p' := by
  rw [List.lookup_append]
  split_ifs with h
  · subst h
    simp [hp]
  · have hne : (p' == p) = false := beq_eq_false_iff_ne.mpr h
    have hnil : List.lookup p' [(p, v)] = none := by rw [List.lookup_cons, hne]; rfl
    rw [hnil, Option.or_none]

end Upstream

/-! ### The libraries with the oracle sampled lazily -/

namespace Lazy

open Probability.Distribution

/-- **The state of the libraries and of the reduction** after the first query. -/
structure State (bits : ℕ) (Salt M : Type) where
  /-- The key `(N, e, d)`. -/
  key : RSA.Key bits
  /-- The table `H` of the oracle: the points defined so far, each with its value `Y` and, at a
  point programmed by a signature query, its root `S`. -/
  H : List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits))
  /-- The signatures issued, `𝒮`. -/
  signed : List (M × Salt × RSA.Residue bits)
  /-- Whether a signature query has hit a point defined by an oracle or a verification query. -/
  bad : Bool

variable {Salt : Type} [Fintype Salt] [Nonempty Salt] [DecidableEq Salt]
  {M : Type} [Fintype M] [DecidableEq M]

/-- The state with the point `p` defined, of value `Y`, without a root. -/
def State.define (s : State bits Salt M) (p : M × Salt) (Y : RSA.Residue bits) :
    State bits Salt M :=
  ⟨s.key, s.H ++ [(p, Y, none)], s.signed, s.bad⟩

/-- A step on the states after the first query, with the signing rule `sign` and the verification
rule `verify`: `pk()` returns `(N, e)`; `sign(m)` samples `R ← Salt` and a residue `z ← ℤ_N` and
follows `sign`; `ver(m, (R, S))` and `ro(m, R)` define `m ‖ R` at a uniform value if it is new, and
`ver` answers with `verify` at its value and root. -/
def stepOn
    (sign : State bits Salt M → M → Salt → RSA.Residue bits →
      State bits Salt M × (Salt × RSA.Residue bits))
    (verify : State bits Salt M → M × Salt × RSA.Residue bits →
      RSA.Residue bits × Option (RSA.Residue bits) → Bool)
    (s : State bits Salt M) :
    (i : SigningRO.Port) → SigRO.Input bits Salt M i →
      Distribution.ProbDist (State bits Salt M × SigRO.Output bits Salt i)
  | .pk, _ => Distribution.ProbDist.single (s, (s.key.N, s.key.e))
  | .sign, m => Distribution.ProbDist.bind (DSL.uniform Salt) fun R =>
      Distribution.ProbDist.map (sign s m R) (RSA.residue s.key.N)
  | .ver, (m, R, S) => match s.H.lookup (m, R) with
    | some v => Distribution.ProbDist.single (s, verify s (m, R, S) v)
    | none => Distribution.ProbDist.map (fun Y =>
        (s.define (m, R) Y, verify (s.define (m, R) Y) (m, R, S) (Y, none))) (RSA.residue s.key.N)
  | .ro, (m, R) => match s.H.lookup (m, R) with
    | some v => Distribution.ProbDist.single (s, v.1)
    | none => Distribution.ProbDist.map (fun Y => (s.define (m, R) Y, Y)) (RSA.residue s.key.N)

/-- **The lazy automaton**: it samples the key at the first query, then steps as
`stepOn sign verify`. -/
def step (keyGen : Distribution.ProbDist (RSA.Key bits))
    (sign : State bits Salt M → M → Salt → RSA.Residue bits →
      State bits Salt M × (Salt × RSA.Residue bits))
    (verify : State bits Salt M → M × Salt × RSA.Residue bits →
      RSA.Residue bits × Option (RSA.Residue bits) → Bool) :
    ProbStep (Option (State bits Salt M)) SigningRO.Port (SigRO.Input bits Salt M)
      (SigRO.Output bits Salt)
  | none, i, x => Distribution.ProbDist.map (Prod.map some id)
      (Distribution.ProbDist.bind keyGen fun key => stepOn sign verify ⟨key, [], [], false⟩ i x)
  | some s, i, x => Distribution.ProbDist.map (Prod.map some id) (stepOn sign verify s i x)

/-- **Signing in the libraries**: at a point already defined, of value `Y`, return `Y^d`, failing
at a point without a root; at a new point, define it at the uniform `Y` and return `Y^d`. -/
def signLibrary (s : State bits Salt M) (m : M) (R : Salt) (Y : RSA.Residue bits) :
    State bits Salt M × (Salt × RSA.Residue bits) :=
  match s.H.lookup (m, R) with
  | some (Y', r) => (⟨s.key, s.H, s.signed ++ [(m, R, s.key.pow Y' s.key.d.val)],
      s.bad || r.isNone⟩, (R, s.key.pow Y' s.key.d.val))
  | none => (⟨s.key, s.H ++ [((m, R), Y, some (s.key.pow Y s.key.d.val))],
      s.signed ++ [(m, R, s.key.pow Y s.key.d.val)], s.bad⟩, (R, s.key.pow Y s.key.d.val))

/-- **Signing in the reduction**: at a point it programmed, return its root; at a point without a
root, fail and return the uniform `S`; at a new point, program it at `S^e` and return `S`. -/
def signReduction (s : State bits Salt M) (m : M) (R : Salt) (S : RSA.Residue bits) :
    State bits Salt M × (Salt × RSA.Residue bits) :=
  match s.H.lookup (m, R) with
  | some (_, some S₀) => (⟨s.key, s.H, s.signed ++ [(m, R, S₀)], s.bad⟩, (R, S₀))
  | some (_, none) => (⟨s.key, s.H, s.signed ++ [(m, R, S)], true⟩, (R, S))
  | none => (⟨s.key, s.H ++ [((m, R), s.key.pow S s.key.e.val, some S)],
      s.signed ++ [(m, R, S)], s.bad⟩, (R, S))

/-- Verification in `sig-real+ro`: `RO(m ‖ R) = S^e mod N`, for a residue `S`. -/
def verifyReal (s : State bits Salt M) (x : M × Salt × RSA.Residue bits)
    (v : RSA.Residue bits × Option (RSA.Residue bits)) : Bool :=
  decide (x.2.2.val < s.key.N.val ∧ v.1 = s.key.pow x.2.2 s.key.e.val)

/-- Verification in `sig-fake`: `(m, R, S) ∈ 𝒮`. -/
def verifyFake (s : State bits Salt M) (x : M × Salt × RSA.Residue bits)
    (_ : RSA.Residue bits × Option (RSA.Residue bits)) : Bool :=
  decide (x ∈ s.signed)

/-- Verification in the reduction, on a library whose `check*(S)` is `chk`: the verification
equation at a programmed point, and through `check*(S)` at a point without a root. -/
def verifyReduction (chk : RSA.Key bits → List ((M × Salt) × RSA.Residue bits ×
      Option (RSA.Residue bits)) → RSA.Residue bits → Bool)
    (s : State bits Salt M) (x : M × Salt × RSA.Residue bits)
    (v : RSA.Residue bits × Option (RSA.Residue bits)) : Bool :=
  match v.2 with
  | some _ => decide (x.2.2.val < s.key.N.val ∧ v.1 = s.key.pow x.2.2 s.key.e.val)
  | none => if x.2.2.val < s.key.N.val ∧ v.1 = s.key.pow x.2.2 s.key.e.val then
      chk s.key s.H x.2.2 else false

/-- The challenges among the values of a table: the values of the points without a root. -/
def challenges (table : List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits))) :
    List (RSA.Residue bits) :=
  table.filterMap fun e => if e.2.2 = none then some e.2.1 else none

omit [Fintype M] [DecidableEq M] [Fintype Salt] [Nonempty Salt] [DecidableEq Salt] in
/-- A new point without a root adds its value to the challenges. -/
lemma challenges_append_none
    (table : List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits)))
    (p : M × Salt) (Y : RSA.Residue bits) :
    challenges (table ++ [(p, Y, none)]) = challenges table ++ [Y] := by
  simp [challenges, List.filterMap_append]

omit [Fintype M] [DecidableEq M] [Fintype Salt] [Nonempty Salt] [DecidableEq Salt] in
/-- A programmed point leaves the challenges unchanged. -/
lemma challenges_append_some
    (table : List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits)))
    (p : M × Salt) (Y S : RSA.Residue bits) :
    challenges (table ++ [(p, Y, some S)]) = challenges table := by
  simp [challenges, List.filterMap_append]


section Oracle

/-- The value of the oracle at a point, at the modulus of the key: the value the table gives
it, and a uniform residue at a point the table does not define. -/
def oracleEntry (key : RSA.Key bits)
    (table : List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits)))
    (p : M × Salt) : Distribution (RSA.Residue bits) :=
  match table.lookup p with
  | some v => Finsupp.single v.1 1
  | none => (RSA.residue key.N).1

/-- **The oracle of a table**: at the modulus of the key, the values of the table and uniform
residues at the other points; at the other moduli, uniform residues. -/
def oracle (key : RSA.Key bits)
    (table : List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits))) :
    Distribution (RSA.Residue bits → M × Salt → RSA.Residue bits) :=
  pi (Function.update (fun N => pi fun _ : M × Salt => (RSA.residue N).1) key.N
    (pi (oracleEntry key table)))

omit [Nonempty Salt] in
/-- The oracle of a table is a probability law. -/
lemma oracle_isProbDist (key : RSA.Key bits)
    (table : List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits))) :
    (oracle key table).isProbDist := by
  refine pi_isProbDist fun N => ?_
  by_cases hN : N = key.N
  · subst hN
    rw [Function.update_self]
    refine pi_isProbDist fun p => ?_
    unfold oracleEntry
    split
    · exact isProbDist_single _
    · exact (RSA.residue _).2
  · rw [Function.update_of_ne hN]
    exact pi_isProbDist fun _ => (RSA.residue N).2

omit [Nonempty Salt] in
/-- With nothing defined, the oracle of a table is the uniform oracle. -/
lemma oracle_nil (key : RSA.Key bits) :
    oracle (Salt := Salt) (M := M) key [] =
      (residueOracles (bits := bits) (M × Salt)).1 := by
  unfold oracle
  have he : oracleEntry (Salt := Salt) (M := M) key [] = fun _ => (RSA.residue key.N).1 := by
    funext p
    simp [oracleEntry]
  rw [he]
  have hu : Function.update (fun N => pi fun _ : M × Salt => (RSA.residue N).1) key.N
      (pi fun _ : M × Salt => (RSA.residue key.N).1) =
        fun N => pi fun _ : M × Salt => (RSA.residue N).1 :=
    Function.update_eq_self _ _
  rw [hu]
  rfl

omit [Nonempty Salt] in
/-- A point a table defines has its value under the oracle of the table. -/
lemma eq_of_mem_support_oracle {key : RSA.Key bits}
    {table : List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits))}
    {ROs : RSA.Residue bits → M × Salt → RSA.Residue bits}
    (hROs : ROs ∈ (oracle key table).support) {p : M × Salt}
    {v : RSA.Residue bits × Option (RSA.Residue bits)} (hp : table.lookup p = some v) :
    ROs key.N p = v.1 := by
  rw [Finsupp.mem_support_iff, oracle, pi_apply] at hROs
  have hN := Finset.prod_ne_zero_iff.mp hROs key.N (Finset.mem_univ _)
  rw [Function.update_self, pi_apply] at hN
  have hP := Finset.prod_ne_zero_iff.mp hN p (Finset.mem_univ _)
  rw [oracleEntry, hp] at hP
  by_contra hne
  exact hP (Finsupp.single_eq_of_ne hne)

omit [Nonempty Salt] in
/-- **Lazy sampling of the oracle**: at a point the table does not define, the oracle of the
table samples the value of the point uniformly and is the oracle of the table defining it there. -/
lemma oracle_eq_bindK {key : RSA.Key bits}
    {table : List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits))}
    {p : M × Salt} (hp : table.lookup p = none)
    (r : RSA.Residue bits → Option (RSA.Residue bits)) :
    oracle key table = bindK (RSA.residue key.N).1 fun Y =>
      oracle key (table ++ [(p, Y, r Y)]) := by
  -- Sampling the coordinate `i` of independent samples, as a mixture over a law of it.
  have hupd : ∀ {ι A : Type} [Fintype ι] [DecidableEq ι] (μ : ι → Distribution A) (i : ι)
      (ρ : Distribution (RSA.Residue bits)) (f : RSA.Residue bits → Distribution A),
      pi (Function.update μ i (bindK ρ f)) = bindK ρ fun z => pi (Function.update μ i (f z)) := by
    intro ι A _ _ μ i ρ f
    have hpi : ∀ X : Distribution A, pi (Function.update μ i X) =
        bindK X fun t => pi (Function.update μ i (Finsupp.single t 1)) := fun X => by
      rw [pi_eq_bindK_update _ i, Function.update_self]
      simp only [Function.update_idem]
    rw [hpi, bindK_bindK]
    exact bindK_congr fun z _ => (hpi (f z)).symm
  have hE : ∀ Y, oracleEntry key (table ++ [(p, Y, r Y)]) =
      Function.update (oracleEntry key table) p (Finsupp.single Y 1) := fun Y => by
    funext p'
    by_cases hp' : p' = p
    · subst hp'
      simp [oracleEntry, List.lookup_append, hp]
    · rw [Function.update_of_ne hp']
      have hne : (p' == p) = false := by simpa using hp'
      have hnil : List.lookup p' [(p, Y, r Y)] = none := by rw [List.lookup_cons, hne]; rfl
      simp [oracleEntry, List.lookup_append, hnil]
  unfold oracle
  conv_lhs => rw [pi_eq_bindK_update (oracleEntry key table) p]
  rw [show oracleEntry key table p = (RSA.residue key.N).1 by simp [oracleEntry, hp], hupd]
  simp only [hE]

end Oracle

section Automaton

variable (keyGen : Distribution.ProbDist (RSA.Key bits))
  (sign : State bits Salt M → M → Salt → RSA.Residue bits →
    State bits Salt M × (Salt × RSA.Residue bits))
  (verify : State bits Salt M → M × Salt × RSA.Residue bits →
    RSA.Residue bits × Option (RSA.Residue bits) → Bool)

/-- A step of the lazy automaton after the first query is a step on the initialized states. -/
lemma step_outcome_some (s : State bits Salt M) (x : Σ i, SigRO.Input bits Salt M i) :
    (step keyGen sign verify).outcome (some s) x =
      fTransform (fun p => (some p.1, (⟨x.1, p.2⟩ : Σ i, SigRO.Output bits Salt i)))
        (stepOn sign verify s x.1 x.2).1 := by
  rw [ProbStep.outcome]
  change fTransform _ (fTransform _ _) = _
  rw [fTransform_fTransform]
  rfl

/-- The first step of the lazy automaton samples the key, then steps as from nothing defined. -/
lemma step_outcome_none (x : Σ i, SigRO.Input bits Salt M i) :
    (step keyGen sign verify).outcome none x =
      bindK keyGen.1 fun key =>
        (step keyGen sign verify).outcome (some ⟨key, [], [], false⟩) x := by
  rw [ProbStep.outcome]
  change fTransform _ (fTransform _ (Distribution.ProbDist.bind keyGen _).1) = _
  rw [Distribution.ProbDist.bind_val, fTransform_bindK, fTransform_bindK]
  refine bindK_congr fun key _ => ?_
  rw [step_outcome_some, fTransform_fTransform]
  rfl

/-- **A simulation at the first query**: if the kernel sends the empty state to `r₀`, from which
`step₂` samples the key and steps as from the kernel image of the state of that key with nothing
defined, and the steps from those states are simulated, so is the first step. -/
lemma step_simulatesAt_none {S₂ : Type}
    (step₂ : ProbStep S₂ SigningRO.Port (SigRO.Input bits Salt M) (SigRO.Output bits Salt))
    (K : Option (State bits Salt M) → Distribution.ProbDist S₂) {r₀ : S₂}
    (hK : (K none).1 = Finsupp.single r₀ 1)
    (h₀ : ∀ x, step₂.outcome r₀ x = bindK keyGen.1 fun key =>
      bindK (K (some ⟨key, [], [], false⟩)).1 fun r => step₂.outcome r x)
    (hsome : ∀ key x, ProbStep.SimulatesAt (step keyGen sign verify) step₂ K
      (some ⟨key, [], [], false⟩) x) (x : Σ i, SigRO.Input bits Salt M i) :
    ProbStep.SimulatesAt (step keyGen sign verify) step₂ K none x := by
  unfold ProbStep.SimulatesAt at hsome ⊢
  rw [hK, bindK_single, one_smul, h₀, step_outcome_none, bindK_bindK]
  exact bindK_congr fun key _ => hsome key x

/-- `pk()`: the public key. -/
lemma stepOn_pk (s : State bits Salt M) (u : SigRO.Input bits Salt M .pk) :
    (stepOn sign verify s .pk u).1 = Finsupp.single (s, (s.key.N, s.key.e)) 1 := rfl

/-- `sign(m)`: uniform `R` and `z ∈ ℤ_N`, then the signing rule. -/
lemma stepOn_sign (s : State bits Salt M) (m : M) :
    (stepOn sign verify s .sign m).1 = bindK (DSL.uniform Salt).1 fun R =>
      fTransform (sign s m R) (RSA.residue s.key.N).1 :=
  Distribution.ProbDist.bind_val _ _

/-- `ver(m, (R, S))` at a defined point: the verification rule at its value and root. -/
lemma stepOn_ver_some {s : State bits Salt M} {m : M} {R : Salt}
    {v : RSA.Residue bits × Option (RSA.Residue bits)} (hp : s.H.lookup (m, R) = some v)
    (S : RSA.Residue bits) :
    (stepOn sign verify s .ver (m, R, S)).1 = Finsupp.single (s, verify s (m, R, S) v) 1 := by
  simp [stepOn, hp]
  rfl

/-- `ver(m, (R, S))` at a new point: define it at a uniform value, then verify. -/
lemma stepOn_ver_none {s : State bits Salt M} {m : M} {R : Salt}
    (hp : s.H.lookup (m, R) = none) (S : RSA.Residue bits) :
    (stepOn sign verify s .ver (m, R, S)).1 = fTransform (fun Y =>
      (s.define (m, R) Y, verify (s.define (m, R) Y) (m, R, S) (Y, none)))
        (RSA.residue s.key.N).1 := by
  simp [stepOn, hp]
  rfl

/-- `ro(m, R)` at a defined point: its value. -/
lemma stepOn_ro_some {s : State bits Salt M} {m : M} {R : Salt}
    {v : RSA.Residue bits × Option (RSA.Residue bits)} (hp : s.H.lookup (m, R) = some v) :
    (stepOn sign verify s .ro (m, R)).1 = Finsupp.single (s, v.1) 1 := by
  simp [stepOn, hp]
  rfl

/-- `ro(m, R)` at a new point: define it at a uniform value and return it. -/
lemma stepOn_ro_none {s : State bits Salt M} {m : M} {R : Salt}
    (hp : s.H.lookup (m, R) = none) :
    (stepOn sign verify s .ro (m, R)).1 =
      fTransform (fun Y => (s.define (m, R) Y, Y)) (RSA.residue s.key.N).1 := by
  simp [stepOn, hp]
  rfl

end Automaton

end Lazy

/-! ### Steps of programs on fresh samples -/

/-- A call of a program to one of its fresh sources, in the computation of its step: the call,
and the sample the source draws. -/
local macro "fresh_call " body:ident q:term : tactic => `(tactic| (
  rw [Program.probInvoke_succ_inr (q := $q)
    (by simp [$body:ident, callProg, ProbStep.inlReply, ProbStep.inrReply, ProbStep.tagged])]
  repeat (first | rw [ProbStep.outcome_parallel_inl] | rw [ProbStep.outcome_parallel_inr])
  simp only [ProbStep.outcome, ProbStep.fresh, Probability.Distribution.fTransform_fTransform,
    Probability.Distribution.bindK_fTransform, Function.comp_def,
    Probability.Distribution.fTransform_bindK]))

/-- The reply of a program at the port `o`, in the computation of its step. -/
local macro "fresh_return " body:ident o:term:max a:term:max : tactic => `(tactic| (
  rw [Program.probInvoke_inl (o := $o) (a := $a)
    (by simp [$body:ident, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply,
      ProbStep.tagged])]
  simp [Probability.Distribution.fTransform, ProbStep.tagged]))

/-! ### The libraries as the lazy automaton -/

section Libraries

open Probability.Distribution

variable (Salt : Type) [Fintype Salt] [Nonempty Salt] [DecidableEq Salt]
  (M : Type) [Fintype M] [DecidableEq M]
    (keyGen : Distribution.ProbDist (RSA.Key bits)) (q : SigningRO.Port → ℕ)

/-! #### `sig-real+ro` -/

/-- **`sig-real+ro` sampling afresh**: its program against fresh samples of its laws. -/
def SigReal.freshStep : ProbStep (Option (RSA.Key bits × (RSA.Residue bits → M × Salt →
      RSA.Residue bits)) × (Unit × (Unit × Unit))) SigningRO.Port (SigRO.Input bits Salt M)
      (SigRO.Output bits Salt) :=
  (SigReal.Library.body Salt M keyGen).probCombine (ProbStep.parallel
    (ProbStep.fresh (SigReal.Library.law1 Salt M keyGen)) (ProbStep.parallel
      (ProbStep.fresh (SigReal.Library.law2 Salt M keyGen))
      (ProbStep.fresh (SigReal.Library.law3 Salt M keyGen))))
    (SigReal.Library.bound_spec Salt M keyGen)

/-- The notes' `sig-real+ro` is the automaton sampling afresh. -/
lemma SigReal.Library.perPort_eq_fresh :
    SigReal.Library.perPort Salt M keyGen (budget := q) = Resource.ofProbAutomaton _
      (SigReal.freshStep Salt M keyGen) (Distribution.ProbDist.single (none, ((), ((), ())))) :=
  (((FreshSampling.source (SigReal.Library.law1 Salt M keyGen) _).parallel
    ((FreshSampling.source (SigReal.Library.law2 Salt M keyGen) _).parallel
      (FreshSampling.source (SigReal.Library.law3 Salt M keyGen) _))).ofProgram none _ _ _).eq_fresh

section SigRealSteps

variable (key : RSA.Key bits) (ROs : RSA.Residue bits → M × Salt → RSA.Residue bits)

/-- `pk()` in `sig-real+ro`, sampled afresh: `(N, e)`. -/
lemma SigReal.outcome_pk :
    (SigReal.freshStep Salt M keyGen).outcome (some (key, ROs), ((), ((), ()))) ⟨.pk, ()⟩ =
      Finsupp.single ((some (key, ROs), ((), ((), ()))),
        (⟨.pk, (key.N, key.e)⟩ : Σ i, SigRO.Output bits Salt i)) 1 := by
  rw [SigReal.freshStep, ProbStep.outcome, Program.probCombine_val]
  fresh_return SigReal.Library.body SigningRO.Port.pk (some (key, ROs), (key.N, key.e))

/-- `sign(m)` in `sig-real+ro`, sampled afresh: a uniform `R` and `RO(m ‖ R)^d`. -/
lemma SigReal.outcome_sign (m : M) :
    (SigReal.freshStep Salt M keyGen).outcome (some (key, ROs), ((), ((), ()))) ⟨.sign, m⟩ =
      bindK (SigReal.Library.law3 Salt M keyGen).1 fun R =>
        Finsupp.single ((some (key, ROs), ((), ((), ()))),
          (⟨.sign, (R, key.pow (ROs key.N (m, R)) key.d.val)⟩ :
            Σ i, SigRO.Output bits Salt i)) 1 := by
  rw [SigReal.freshStep, ProbStep.outcome, Program.probCombine_val,
    show SigReal.Library.bound Salt M keyGen = 2 + 1 from rfl]
  fresh_call SigReal.Library.body ⟨.inr (.inr ()), ()⟩
  refine bindK_congr fun R _ => ?_
  fresh_return SigReal.Library.body SigningRO.Port.sign
    (some (key, ROs), (R, key.pow (ROs key.N (m, R)) key.d.val))

/-- `ver(m, (R, S))` in `sig-real+ro`, sampled afresh: the verification equation. -/
lemma SigReal.outcome_ver (m : M) (R : Salt) (S : RSA.Residue bits) :
    (SigReal.freshStep Salt M keyGen).outcome (some (key, ROs), ((), ((), ())))
        ⟨.ver, (m, R, S)⟩ =
      Finsupp.single ((some (key, ROs), ((), ((), ()))),
        (⟨.ver, decide (S.val < key.N.val ∧ ROs key.N (m, R) = key.pow S key.e.val)⟩ :
          Σ i, SigRO.Output bits Salt i)) 1 := by
  rw [SigReal.freshStep, ProbStep.outcome, Program.probCombine_val]
  fresh_return SigReal.Library.body SigningRO.Port.ver
    (some (key, ROs), decide (S.val < key.N.val ∧ ROs key.N (m, R) = key.pow S key.e.val))

/-- `ro(m, R)` in `sig-real+ro`, sampled afresh: `RO(m ‖ R)`. -/
lemma SigReal.outcome_ro (m : M) (R : Salt) :
    (SigReal.freshStep Salt M keyGen).outcome (some (key, ROs), ((), ((), ()))) ⟨.ro, (m, R)⟩ =
      Finsupp.single ((some (key, ROs), ((), ((), ()))),
        (⟨.ro, ROs key.N (m, R)⟩ : Σ i, SigRO.Output bits Salt i)) 1 := by
  rw [SigReal.freshStep, ProbStep.outcome, Program.probCombine_val]
  fresh_return SigReal.Library.body SigningRO.Port.ro (some (key, ROs), ROs key.N (m, R))

end SigRealSteps

/-- **The first query of `sig-real+ro`**, sampled afresh: it samples the key and the oracle, then
answers as from them. -/
lemma SigReal.outcome_none (x : Σ i, SigRO.Input bits Salt M i) :
    (SigReal.freshStep Salt M keyGen).outcome (none, ((), ((), ()))) x =
      bindK keyGen.1 fun key => bindK (residueOracles (bits := bits) (M × Salt)).1
        fun ROs => (SigReal.freshStep Salt M keyGen).outcome
          (some (key, ROs), ((), ((), ()))) x := by
  obtain ⟨_ | _ | _ | _, x⟩ := x
  · cases x
    simp only [SigReal.outcome_pk]
    rw [SigReal.freshStep, ProbStep.outcome, Program.probCombine_val,
      show SigReal.Library.bound Salt M keyGen = 2 + 1 from rfl]
    fresh_call SigReal.Library.body ⟨.inl (), ()⟩
    refine bindK_congr fun key _ => ?_
    fresh_call SigReal.Library.body ⟨.inr (.inl ()), ()⟩
    refine bindK_congr fun ROs _ => ?_
    fresh_return SigReal.Library.body SigningRO.Port.pk
      (some (key, ROs), (RSA.Key.N key, RSA.Key.e key))
  · simp only [SigReal.outcome_sign]
    rw [SigReal.freshStep, ProbStep.outcome, Program.probCombine_val,
      show SigReal.Library.bound Salt M keyGen = 2 + 1 from rfl]
    fresh_call SigReal.Library.body ⟨.inl (), ()⟩
    refine bindK_congr fun key _ => ?_
    fresh_call SigReal.Library.body ⟨.inr (.inl ()), ()⟩
    refine bindK_congr fun ROs _ => ?_
    fresh_call SigReal.Library.body ⟨.inr (.inr ()), ()⟩
    refine bindK_congr fun R _ => ?_
    fresh_return SigReal.Library.body SigningRO.Port.sign
      (some (key, ROs), (R, RSA.Key.pow key (ROs (RSA.Key.N key) (x, R)) (RSA.Key.d key).val))
  · obtain ⟨m, R, S⟩ := x
    simp only [SigReal.outcome_ver]
    rw [SigReal.freshStep, ProbStep.outcome, Program.probCombine_val,
      show SigReal.Library.bound Salt M keyGen = 2 + 1 from rfl]
    fresh_call SigReal.Library.body ⟨.inl (), ()⟩
    refine bindK_congr fun key _ => ?_
    fresh_call SigReal.Library.body ⟨.inr (.inl ()), ()⟩
    refine bindK_congr fun ROs _ => ?_
    fresh_return SigReal.Library.body SigningRO.Port.ver (some (key, ROs),
      decide (S.val < (RSA.Key.N key).val ∧
        ROs (RSA.Key.N key) (m, R) = RSA.Key.pow key S (RSA.Key.e key).val))
  · obtain ⟨m, R⟩ := x
    simp only [SigReal.outcome_ro]
    rw [SigReal.freshStep, ProbStep.outcome, Program.probCombine_val,
      show SigReal.Library.bound Salt M keyGen = 2 + 1 from rfl]
    fresh_call SigReal.Library.body ⟨.inl (), ()⟩
    refine bindK_congr fun key _ => ?_
    fresh_call SigReal.Library.body ⟨.inr (.inl ()), ()⟩
    refine bindK_congr fun ROs _ => ?_
    fresh_return SigReal.Library.body SigningRO.Port.ro
      (some (key, ROs), ROs (RSA.Key.N key) (m, R))

/-- **`sig-real+ro` at a key and an oracle**, sampled afresh: the scheme's oracles under the key
`(N, e, d)` and the oracle at `N`, beside it, step as the notes' library from that key and
oracle. -/
lemma SigReal.outcome_forward (key : RSA.Key bits)
    (ROs : RSA.Residue bits → M × Salt → RSA.Residue bits)
    (s : Option Unit × ((Option Unit × Unit) × Unit)) (x : Σ i, SigRO.Input bits Salt M i) :
    (SigReal.freshStep Salt M keyGen).outcome (some (key, ROs), ((), ((), ()))) x =
      fTransform (Prod.map (fun _ => (some (key, ROs), ((), ((), ())))) id)
        (((SignatureSchemeRO.Forward.body _ _ _ _ _).probCombine (ProbStep.parallel
          ((SignatureSchemeRO.Fixed.body _ _ _ _ _ _ (scheme Salt M) key (ROs key.N)).probCombine
            (ProbStep.fresh (SignatureSchemeRO.Fixed.law1 _ _ _ _ _ _ (scheme Salt M) key
              (ROs key.N)))
            (SignatureSchemeRO.Fixed.bound_spec _ _ _ _ _ _ (scheme Salt M) key (ROs key.N)))
          (ProbStep.ofDeterministic fun (_ : Unit)
            (_ : (Evaluation (M × Salt) (RSA.Residue bits) 0).I) a => ((), ROs key.N a)))
          (SignatureSchemeRO.Forward.bound_spec _ _ _ _ _)).outcome s x) := by
  obtain ⟨sW, ⟨sF, ⟨⟩⟩, ⟨⟩⟩ := s
  obtain ⟨_ | _ | _ | _, x⟩ := x
  · cases x
    rw [SigReal.outcome_pk]
    simp only [ProbStep.outcome]
    rw [SignatureSchemeRO.Forward.step_pk, SignatureSchemeRO.Fixed.step_publicKey]
    simp [fTransform, ProbStep.tagged, scheme]
  · rw [SigReal.outcome_sign]
    simp only [ProbStep.outcome]
    rw [SignatureSchemeRO.Forward.step_sign, SignatureSchemeRO.Fixed.step_sign]
    simp only [scheme, Distribution.ProbDist.map, fTransform_fTransform]
    rw [fTransform_eq_bindK]
    rfl
  · obtain ⟨m, R, S⟩ := x
    rw [SigReal.outcome_ver]
    simp only [ProbStep.outcome]
    rw [SignatureSchemeRO.Forward.step_ver, SignatureSchemeRO.Fixed.step_verify]
    simp [fTransform, ProbStep.tagged, scheme, RSA.powMod_eq_pow]
  · rw [SigReal.outcome_ro]
    simp only [ProbStep.outcome]
    rw [SignatureSchemeRO.Forward.step_ro]
    simp [fTransform, ProbStep.tagged, ProbStep.ofDeterministic, Distribution.ProbDist.single]

/-- **`sig-real+ro` at a key and an oracle is the notes' library from them**: the scheme's
oracles under `(N, e, d)` and the oracle at `N`, beside it, are the library started at that key
and oracle. -/
lemma SigReal.forward_fixed (key : RSA.Key bits)
    (ROs : RSA.Residue bits → M × Salt → RSA.Residue bits) :
    SignatureSchemeRO.Forward.perLabel q •
        (SignatureSchemeRO.Fixed.perPort _ _ _ _ _ _ (scheme Salt M) key (ROs key.N) ∥
          Resource.ofFunction (A := Evaluation (M × Salt) (RSA.Residue bits) (q .ro))
            fun _ => ROs key.N) =
      Resource.ofProbAutomaton _ (SigReal.freshStep Salt M keyGen)
        (Distribution.ProbDist.single (some (key, ROs), ((), ((), ())))) := by
  refine ((((FreshSampling.source (SignatureSchemeRO.Fixed.law1 _ _ _ _ _ _ (scheme Salt M) key
    (ROs key.N)) _).ofProgram none _ _ _).parallel
      (FreshSampling.ofFunction _)).ofLabelBoundedProgram none _ _ _
        SignatureSchemeRO.Forward.labelBounded q _
          (SignatureSchemeRO.Forward.admits q)).eq_fresh.trans ?_
  refine Resource.ofProbAutomaton_eq_of_map _ _ _ _ (fun _ => (some (key, ROs), ((), ((), ()))))
    (fun s x => SigReal.outcome_forward Salt M keyGen key ROs s x) ?_
  simp [fTransform, Distribution.ProbDist.single]

/-- After the first query, the notes' `sig-real+ro` sampled afresh keeps its state. -/
lemma SigReal.state_of_mem_outcome (c : RSA.Key bits × (RSA.Residue bits → M × Salt →
      RSA.Residue bits)) (x : Σ i, SigRO.Input bits Salt M i)
    {p : (Option (RSA.Key bits × (RSA.Residue bits → M × Salt → RSA.Residue bits)) ×
      (Unit × (Unit × Unit))) × Σ i, SigRO.Output bits Salt i}
    (hp : p ∈ ((SigReal.freshStep Salt M keyGen).outcome (some c, ((), ((), ()))) x).support) :
    p.1 = (some c, ((), ((), ()))) := by
  obtain ⟨key, ROs⟩ := c
  obtain ⟨_ | _ | _ | _, x⟩ := x
  · cases x
    rw [SigReal.outcome_pk] at hp
    exact congrArg Prod.fst (Finset.mem_singleton.mp (Finsupp.support_single_subset hp))
  · rw [SigReal.outcome_sign] at hp
    obtain ⟨R, -, hR⟩ := mem_support_bindK hp
    exact congrArg Prod.fst (Finset.mem_singleton.mp (Finsupp.support_single_subset hR))
  · obtain ⟨m, R, S⟩ := x
    rw [SigReal.outcome_ver] at hp
    exact congrArg Prod.fst (Finset.mem_singleton.mp (Finsupp.support_single_subset hp))
  · obtain ⟨m, R⟩ := x
    rw [SigReal.outcome_ro] at hp
    exact congrArg Prod.fst (Finset.mem_singleton.mp (Finsupp.support_single_subset hp))

/-- **The initialization of the notes' `sig-real+ro`**, sampled afresh: it samples the key and
the oracle once, then answers as from them. -/
lemma SigReal.ofProbAutomaton_none :
    Resource.ofProbAutomaton (SigRO.perPort bits Salt M q) (SigReal.freshStep Salt M keyGen)
        (Distribution.ProbDist.single (none, ((), ((), ())))) =
      Resource.ofProbAutomaton _ (SigReal.freshStep Salt M keyGen)
        ⟨fTransform (fun c => (some c, ((), ((), ()))))
            (prod keyGen.1 (residueOracles (bits := bits) (M × Salt)).1),
          fTransform_isProbDist _ (Distribution.IsProbability.isProbDist _)⟩ := by
  let init : Distribution.ProbDist (Option (RSA.Key bits × (RSA.Residue bits → M × Salt →
      RSA.Residue bits)) × (Unit × (Unit × Unit))) :=
    ⟨fTransform (fun c => (some c, ((), ((), ()))))
        (prod keyGen.1 (residueOracles (bits := bits) (M × Salt)).1),
      fTransform_isProbDist _ (Distribution.IsProbability.isProbDist _)⟩
  let K : Option (RSA.Key bits × (RSA.Residue bits → M × Salt → RSA.Residue bits)) ×
      (Unit × (Unit × Unit)) → Distribution.ProbDist (Option (RSA.Key bits ×
        (RSA.Residue bits → M × Salt → RSA.Residue bits)) × (Unit × (Unit × Unit)))
    | (none, _) => init
    | (some c, u) => Distribution.ProbDist.single (some c, u)
  -- After the first query the kernel keeps the state.
  have hsome : ∀ c x, bindK ((SigReal.freshStep Salt M keyGen).outcome (some c, ((), ((), ()))) x)
      (fun p => fTransform (fun s₂ => (s₂, p.2)) (K p.1).1) =
        (SigReal.freshStep Salt M keyGen).outcome (some c, ((), ((), ()))) x := by
    intro c x
    conv_rhs => rw [← bindK_single_one ((SigReal.freshStep Salt M keyGen).outcome _ x)]
    refine bindK_congr fun p hp => ?_
    have hs := SigReal.state_of_mem_outcome Salt M keyGen c x hp
    obtain ⟨s₁, y⟩ := p
    obtain rfl : s₁ = _ := hs
    simp [K, fTransform, Distribution.ProbDist.single]
  refine Resource.ofProbAutomaton_eq_of_simulation _ _ _ init K (fun _ _ => True)
    (fun _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) (fun _ s x _ _ => ?_) ?_
  · obtain ⟨_ | c, ⟨⟩, ⟨⟩, ⟨⟩⟩ := s
    · unfold ProbStep.SimulatesAt
      rw [SigReal.outcome_none, bindK_bindK]
      simp only [bindK_bindK, hsome]
      change bindK (fTransform _ (prod keyGen.1 _)) _ = _
      rw [bindK_fTransform, prod_eq_bindK, bindK_bindK]
      refine bindK_congr fun key _ => ?_
      rw [bindK_fTransform]
      rfl
    · unfold ProbStep.SimulatesAt
      rw [hsome]
      change bindK (Finsupp.single _ 1) _ = _
      rw [bindK_single, one_smul]
  · change _ = bindK (Finsupp.single _ 1) _
    rw [bindK_single, one_smul]

/-- **`sig-real+ro` is the notes' library** [1, §8.2]: the scheme's oracles beside the oracle,
sampled per key, are the library that samples the key and an oracle for every modulus and
answers at the key's `N`. -/
theorem SigReal.eq_library :
    SigReal Salt M keyGen q = SigReal.Library.perPort Salt M keyGen (budget := q) := by
  rw [SigReal, SignatureSchemeRO.Real, Resource.smul_sample]
  simp only [Resource.smul_sample]
  -- The oracle at `N` is the coordinate `N` of an oracle for every modulus.
  have hkey : ∀ key : RSA.Key bits,
      (Resource.sample (residueOracle (M × Salt) ((scheme Salt M).publicKey key).1).1 fun RO =>
        SignatureSchemeRO.Forward.perLabel q •
          (SignatureSchemeRO.Fixed.perPort _ _ _ _ _ _ (scheme Salt M) key RO ∥
            Resource.ofFunction (A := Evaluation (M × Salt) (RSA.Residue bits) (q .ro))
              fun _ => RO)) =
        Resource.sample (residueOracles (bits := bits) (M × Salt)).1 fun ROs =>
          Resource.ofProbAutomaton _ (SigReal.freshStep Salt M keyGen)
            (Distribution.ProbDist.single (some (key, ROs), ((), ((), ())))) := fun key =>
    (Resource.sample_eq_sample_of_fTransform _ _ (fun ROs => ROs key.N) _ _
      (Distribution.ProbDist.fTransform_eval_pi _ _)
      fun ROs => (SigReal.forward_fixed Salt M keyGen q key ROs).symm).symm
  simp only [hkey]
  rw [Resource.sample_sample, ← Resource.ofProbAutomaton_fTransform,
    SigReal.Library.perPort_eq_fresh, SigReal.ofProbAutomaton_none]

/-- **The kernel to `sig-real+ro`**: the oracle of the table `H`, at the key. -/
def SigReal.kernel : Option (Lazy.State bits Salt M) →
    Distribution.ProbDist (Option (RSA.Key bits × (RSA.Residue bits → M × Salt →
      RSA.Residue bits)) × (Unit × (Unit × Unit)))
  | none => Distribution.ProbDist.single (none, ((), ((), ())))
  | some s => ⟨fTransform (fun ROs => (some (s.key, ROs), ((), ((), ()))))
      (Lazy.oracle s.key s.H), fTransform_isProbDist _ (Lazy.oracle_isProbDist _ _)⟩

omit [Nonempty Salt] in
/-- The kernel to `sig-real+ro` after the first query. -/
lemma SigReal.kernel_some (s : Lazy.State bits Salt M) :
    (SigReal.kernel Salt M (some s)).1 =
      fTransform (fun ROs => (some (s.key, ROs), ((), ((), ())))) (Lazy.oracle s.key s.H) := rfl

/-- **`sig-real+ro` is lazy sampling of its oracle**, at a state after the first query: from the
oracle of `H`, a step of `sig-real+ro` is a step of the lazy library followed by the kernel. -/
lemma SigReal.simulatesAt_some (s : Lazy.State bits Salt M)
    (x : Σ i, SigRO.Input bits Salt M i) :
    ProbStep.SimulatesAt (Lazy.step keyGen Lazy.signLibrary Lazy.verifyReal)
      (SigReal.freshStep Salt M keyGen) (SigReal.kernel Salt M) (some s) x := by
  unfold ProbStep.SimulatesAt
  rw [Lazy.step_outcome_some, bindK_fTransform, SigReal.kernel_some, bindK_fTransform]
  obtain ⟨_ | _ | _ | _, x⟩ := x
  · cases x
    simp only [Function.comp_def, SigReal.outcome_pk, SigReal.kernel_some]
    rw [Lazy.stepOn_pk, bindK_single, one_smul, fTransform_fTransform, ← bindK_single_comp]
    rfl
  · simp only [Function.comp_def, SigReal.outcome_sign, SigReal.kernel_some]
    rw [Lazy.stepOn_sign, bindK_bindK, bindK_comm]
    refine bindK_congr fun R _ => ?_
    rw [bindK_fTransform]
    cases hp : s.H.lookup (x, R) with
    | some v =>
      have hs : ∀ Y, Lazy.signLibrary s x R Y = (⟨s.key, s.H,
          s.signed ++ [(x, R, s.key.pow v.1 s.key.d.val)], s.bad || v.2.isNone⟩,
          (R, s.key.pow v.1 s.key.d.val)) := fun Y => by simp [Lazy.signLibrary, hp]
      simp only [Function.comp_def, hs, fTransform_fTransform]
      rw [bindK_const_of_weight (RSA.residue s.key.N).2.2, fTransform_eq_bindK]
      refine bindK_congr fun ROs hROs => ?_
      rw [Lazy.eq_of_mem_support_oracle hROs hp]
    | none =>
      have hs : ∀ Y, Lazy.signLibrary s x R Y = (⟨s.key, s.H ++ [((x, R), Y,
          some (s.key.pow Y s.key.d.val))], s.signed ++ [(x, R, s.key.pow Y s.key.d.val)], s.bad⟩,
          (R, s.key.pow Y s.key.d.val)) := fun Y => by simp [Lazy.signLibrary, hp]
      simp only [Function.comp_def, hs, fTransform_fTransform]
      rw [Lazy.oracle_eq_bindK hp (fun Y => some (s.key.pow Y s.key.d.val)), bindK_bindK]
      refine bindK_congr fun Y _ => ?_
      rw [fTransform_eq_bindK]
      refine bindK_congr fun ROs hROs => ?_
      rw [Lazy.eq_of_mem_support_oracle hROs (p := (x, R))
        (v := (Y, some (s.key.pow Y s.key.d.val))) (by simp [List.lookup_append, hp])]
  · obtain ⟨m, R, S⟩ := x
    simp only [Function.comp_def, SigReal.outcome_ver, SigReal.kernel_some]
    cases hp : s.H.lookup (m, R) with
    | some v =>
      rw [Lazy.stepOn_ver_some _ _ hp, bindK_single, one_smul, fTransform_fTransform,
        fTransform_eq_bindK]
      refine bindK_congr fun ROs hROs => ?_
      rw [Lazy.eq_of_mem_support_oracle hROs hp]
      rfl
    | none =>
      rw [Lazy.stepOn_ver_none _ _ hp, bindK_fTransform, Lazy.oracle_eq_bindK hp (fun _ => none),
        bindK_bindK]
      refine bindK_congr fun Y _ => ?_
      simp only [Function.comp_def, fTransform_fTransform, Lazy.State.define]
      rw [fTransform_eq_bindK]
      refine bindK_congr fun ROs hROs => ?_
      rw [Lazy.eq_of_mem_support_oracle hROs (p := (m, R)) (v := (Y, none))
        (by simp [List.lookup_append, hp])]
      rfl
  · obtain ⟨m, R⟩ := x
    simp only [Function.comp_def, SigReal.outcome_ro, SigReal.kernel_some]
    cases hp : s.H.lookup (m, R) with
    | some v =>
      rw [Lazy.stepOn_ro_some _ _ hp, bindK_single, one_smul, fTransform_fTransform,
        fTransform_eq_bindK]
      refine bindK_congr fun ROs hROs => ?_
      rw [Lazy.eq_of_mem_support_oracle hROs hp]
      rfl
    | none =>
      rw [Lazy.stepOn_ro_none _ _ hp, bindK_fTransform, Lazy.oracle_eq_bindK hp (fun _ => none),
        bindK_bindK]
      refine bindK_congr fun Y _ => ?_
      simp only [Function.comp_def, fTransform_fTransform, Lazy.State.define]
      rw [fTransform_eq_bindK]
      refine bindK_congr fun ROs hROs => ?_
      rw [Lazy.eq_of_mem_support_oracle hROs (p := (m, R)) (v := (Y, none))
        (by simp [List.lookup_append, hp])]

/-- **`sig-real+ro` with the oracle sampled lazily**: the library is the lazy automaton with the
signing of the libraries and the verification equation. -/
lemma SigReal.eq_lazy :
    SigReal Salt M keyGen q = Resource.ofProbAutomaton _
      (Lazy.step keyGen Lazy.signLibrary Lazy.verifyReal) (Distribution.ProbDist.single none) := by
  rw [SigReal.eq_library, SigReal.Library.perPort_eq_fresh]
  refine (Resource.ofProbAutomaton_eq_of_simulation (T := SigRO.perPort bits Salt M q)
    (Lazy.step keyGen Lazy.signLibrary Lazy.verifyReal)
    (SigReal.freshStep Salt M keyGen) _ _ (SigReal.kernel Salt M) (fun _ _ => True)
    (fun _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) (fun _ s x _ _ => ?_) ?_).symm
  · cases s with
    | none =>
      refine Lazy.step_simulatesAt_none keyGen _ _ _ _ rfl (fun x => ?_)
        (fun key x => SigReal.simulatesAt_some Salt M keyGen _ x) x
      rw [SigReal.outcome_none]
      refine bindK_congr fun key _ => ?_
      rw [SigReal.kernel_some, bindK_fTransform]
      exact congrArg (bindK · _) (Lazy.oracle_nil key).symm
    | some s => exact SigReal.simulatesAt_some Salt M keyGen s x
  · change Finsupp.single _ 1 = bindK (Finsupp.single none 1) _
    rw [bindK_single, one_smul]
    rfl

/-! #### `sig-fake` -/

/-- **`sig-fake` sampling afresh**: its program against fresh samples of its laws. -/
def SigFake.freshStep : ProbStep (Option (RSA.Key bits × (RSA.Residue bits → M × Salt →
      RSA.Residue bits) × List (M × Salt × RSA.Residue bits)) × (Unit × (Unit × Unit)))
      SigningRO.Port (SigRO.Input bits Salt M) (SigRO.Output bits Salt) :=
  (SigFake.body Salt M keyGen).probCombine (ProbStep.parallel
    (ProbStep.fresh (SigFake.law1 Salt M keyGen)) (ProbStep.parallel
      (ProbStep.fresh (SigFake.law2 Salt M keyGen))
      (ProbStep.fresh (SigFake.law3 Salt M keyGen))))
    (SigFake.bound_spec Salt M keyGen)

/-- `sig-fake` is the automaton sampling afresh. -/
lemma SigFake.perPort_eq_fresh :
    SigFake.perPort Salt M keyGen (budget := q) = Resource.ofProbAutomaton _
      (SigFake.freshStep Salt M keyGen) (Distribution.ProbDist.single (none, ((), ((), ())))) :=
  (((FreshSampling.source (SigFake.law1 Salt M keyGen) _).parallel
    ((FreshSampling.source (SigFake.law2 Salt M keyGen) _).parallel
      (FreshSampling.source (SigFake.law3 Salt M keyGen) _))).ofProgram none _ _ _).eq_fresh

section SigFakeSteps

variable (key : RSA.Key bits) (ROs : RSA.Residue bits → M × Salt → RSA.Residue bits)
  (signed : List (M × Salt × RSA.Residue bits))

/-- `pk()` in `sig-fake`, sampled afresh: `(N, e)`. -/
lemma SigFake.outcome_pk :
    (SigFake.freshStep Salt M keyGen).outcome (some (key, ROs, signed), ((), ((), ())))
        ⟨.pk, ()⟩ =
      Finsupp.single ((some (key, ROs, signed), ((), ((), ()))),
        (⟨.pk, (key.N, key.e)⟩ : Σ i, SigRO.Output bits Salt i)) 1 := by
  rw [SigFake.freshStep, ProbStep.outcome, Program.probCombine_val]
  fresh_return SigFake.body SigningRO.Port.pk (some (key, ROs, signed), (key.N, key.e))

/-- `sign(m)` in `sig-fake`, sampled afresh: a uniform `R` and `RO(m ‖ R)^d`, added to `𝒮`. -/
lemma SigFake.outcome_sign (m : M) :
    (SigFake.freshStep Salt M keyGen).outcome (some (key, ROs, signed), ((), ((), ())))
        ⟨.sign, m⟩ =
      bindK (SigFake.law3 Salt M keyGen).1 fun R =>
        Finsupp.single ((some (key, ROs, signed ++ [(m, R, key.pow (ROs key.N (m, R)) key.d.val)]),
          ((), ((), ()))), (⟨.sign, (R, key.pow (ROs key.N (m, R)) key.d.val)⟩ :
            Σ i, SigRO.Output bits Salt i)) 1 := by
  rw [SigFake.freshStep, ProbStep.outcome, Program.probCombine_val,
    show SigFake.bound Salt M keyGen = 2 + 1 from rfl]
  fresh_call SigFake.body ⟨.inr (.inr ()), ()⟩
  refine bindK_congr fun R _ => ?_
  fresh_return SigFake.body SigningRO.Port.sign
    (some (key, ROs, signed ++ [(m, R, key.pow (ROs key.N (m, R)) key.d.val)]),
      (R, key.pow (ROs key.N (m, R)) key.d.val))

/-- `ver(m, (R, S))` in `sig-fake`, sampled afresh: `(m, R, S) ∈ 𝒮`. -/
lemma SigFake.outcome_ver (m : M) (R : Salt) (S : RSA.Residue bits) :
    (SigFake.freshStep Salt M keyGen).outcome (some (key, ROs, signed), ((), ((), ())))
        ⟨.ver, (m, R, S)⟩ =
      Finsupp.single ((some (key, ROs, signed), ((), ((), ()))),
        (⟨.ver, decide ((m, R, S) ∈ signed)⟩ : Σ i, SigRO.Output bits Salt i)) 1 := by
  rw [SigFake.freshStep, ProbStep.outcome, Program.probCombine_val]
  fresh_return SigFake.body SigningRO.Port.ver
    (some (key, ROs, signed), decide ((m, R, S) ∈ signed))

/-- `ro(m, R)` in `sig-fake`, sampled afresh: `RO(m ‖ R)`. -/
lemma SigFake.outcome_ro (m : M) (R : Salt) :
    (SigFake.freshStep Salt M keyGen).outcome (some (key, ROs, signed), ((), ((), ())))
        ⟨.ro, (m, R)⟩ =
      Finsupp.single ((some (key, ROs, signed), ((), ((), ()))),
        (⟨.ro, ROs key.N (m, R)⟩ : Σ i, SigRO.Output bits Salt i)) 1 := by
  rw [SigFake.freshStep, ProbStep.outcome, Program.probCombine_val]
  fresh_return SigFake.body SigningRO.Port.ro (some (key, ROs, signed), ROs key.N (m, R))

end SigFakeSteps

/-- **The first query of `sig-fake`**, sampled afresh: it samples the key and the oracle, then
answers as from them with nothing signed. -/
lemma SigFake.outcome_none (x : Σ i, SigRO.Input bits Salt M i) :
    (SigFake.freshStep Salt M keyGen).outcome (none, ((), ((), ()))) x =
      bindK keyGen.1 fun key => bindK (residueOracles (bits := bits) (M × Salt)).1
        fun ROs => (SigFake.freshStep Salt M keyGen).outcome
          (some (key, ROs, []), ((), ((), ()))) x := by
  obtain ⟨_ | _ | _ | _, x⟩ := x
  · cases x
    simp only [SigFake.outcome_pk]
    rw [SigFake.freshStep, ProbStep.outcome, Program.probCombine_val,
      show SigFake.bound Salt M keyGen = 2 + 1 from rfl]
    fresh_call SigFake.body ⟨.inl (), ()⟩
    refine bindK_congr fun key _ => ?_
    fresh_call SigFake.body ⟨.inr (.inl ()), ()⟩
    refine bindK_congr fun ROs _ => ?_
    fresh_return SigFake.body SigningRO.Port.pk
      (some (key, ROs, []), (RSA.Key.N key, RSA.Key.e key))
  · simp only [SigFake.outcome_sign]
    rw [SigFake.freshStep, ProbStep.outcome, Program.probCombine_val,
      show SigFake.bound Salt M keyGen = 2 + 1 from rfl]
    fresh_call SigFake.body ⟨.inl (), ()⟩
    refine bindK_congr fun key _ => ?_
    fresh_call SigFake.body ⟨.inr (.inl ()), ()⟩
    refine bindK_congr fun ROs _ => ?_
    fresh_call SigFake.body ⟨.inr (.inr ()), ()⟩
    refine bindK_congr fun R _ => ?_
    fresh_return SigFake.body SigningRO.Port.sign
      (some (key, ROs, [] ++ [(x, R, RSA.Key.pow key (ROs (RSA.Key.N key) (x, R))
        (RSA.Key.d key).val)]),
        (R, RSA.Key.pow key (ROs (RSA.Key.N key) (x, R)) (RSA.Key.d key).val))
  · obtain ⟨m, R, S⟩ := x
    simp only [SigFake.outcome_ver]
    rw [SigFake.freshStep, ProbStep.outcome, Program.probCombine_val,
      show SigFake.bound Salt M keyGen = 2 + 1 from rfl]
    fresh_call SigFake.body ⟨.inl (), ()⟩
    refine bindK_congr fun key _ => ?_
    fresh_call SigFake.body ⟨.inr (.inl ()), ()⟩
    refine bindK_congr fun ROs _ => ?_
    fresh_return SigFake.body SigningRO.Port.ver
      (some (key, ROs, []), decide ((m, R, S) ∈ ([] : List (M × Salt × RSA.Residue bits))))
  · obtain ⟨m, R⟩ := x
    simp only [SigFake.outcome_ro]
    rw [SigFake.freshStep, ProbStep.outcome, Program.probCombine_val,
      show SigFake.bound Salt M keyGen = 2 + 1 from rfl]
    fresh_call SigFake.body ⟨.inl (), ()⟩
    refine bindK_congr fun key _ => ?_
    fresh_call SigFake.body ⟨.inr (.inl ()), ()⟩
    refine bindK_congr fun ROs _ => ?_
    fresh_return SigFake.body SigningRO.Port.ro (some (key, ROs, []), ROs (RSA.Key.N key) (m, R))

/-- **The kernel to `sig-fake`**: the oracle of the table `H`, at the key, and the signatures
issued. -/
def SigFake.kernel : Option (Lazy.State bits Salt M) →
    Distribution.ProbDist (Option (RSA.Key bits × (RSA.Residue bits → M × Salt →
      RSA.Residue bits) × List (M × Salt × RSA.Residue bits)) × (Unit × (Unit × Unit)))
  | none => Distribution.ProbDist.single (none, ((), ((), ())))
  | some s => ⟨fTransform (fun ROs => (some (s.key, ROs, s.signed), ((), ((), ()))))
      (Lazy.oracle s.key s.H), fTransform_isProbDist _ (Lazy.oracle_isProbDist _ _)⟩

omit [Nonempty Salt] in
/-- The kernel to `sig-fake` after the first query. -/
lemma SigFake.kernel_some (s : Lazy.State bits Salt M) :
    (SigFake.kernel Salt M (some s)).1 = fTransform
      (fun ROs => (some (s.key, ROs, s.signed), ((), ((), ())))) (Lazy.oracle s.key s.H) := rfl

/-- **`sig-fake` is lazy sampling of its oracle**, at a state after the first query: from the
oracle of `H`, a step of `sig-fake` is a step of the lazy library followed by the kernel. -/
lemma SigFake.simulatesAt_some (s : Lazy.State bits Salt M)
    (x : Σ i, SigRO.Input bits Salt M i) :
    ProbStep.SimulatesAt (Lazy.step keyGen Lazy.signLibrary Lazy.verifyFake)
      (SigFake.freshStep Salt M keyGen) (SigFake.kernel Salt M) (some s) x := by
  unfold ProbStep.SimulatesAt
  rw [Lazy.step_outcome_some, bindK_fTransform, SigFake.kernel_some, bindK_fTransform]
  obtain ⟨_ | _ | _ | _, x⟩ := x
  · cases x
    simp only [Function.comp_def, SigFake.outcome_pk, SigFake.kernel_some]
    rw [Lazy.stepOn_pk, bindK_single, one_smul, fTransform_fTransform, ← bindK_single_comp]
    rfl
  · simp only [Function.comp_def, SigFake.outcome_sign, SigFake.kernel_some]
    rw [Lazy.stepOn_sign, bindK_bindK, bindK_comm]
    refine bindK_congr fun R _ => ?_
    rw [bindK_fTransform]
    cases hp : s.H.lookup (x, R) with
    | some v =>
      have hs : ∀ Y, Lazy.signLibrary s x R Y = (⟨s.key, s.H,
          s.signed ++ [(x, R, s.key.pow v.1 s.key.d.val)], s.bad || v.2.isNone⟩,
          (R, s.key.pow v.1 s.key.d.val)) := fun Y => by simp [Lazy.signLibrary, hp]
      simp only [Function.comp_def, hs, fTransform_fTransform]
      rw [bindK_const_of_weight (RSA.residue s.key.N).2.2, fTransform_eq_bindK]
      refine bindK_congr fun ROs hROs => ?_
      rw [Lazy.eq_of_mem_support_oracle hROs hp]
    | none =>
      have hs : ∀ Y, Lazy.signLibrary s x R Y = (⟨s.key, s.H ++ [((x, R), Y,
          some (s.key.pow Y s.key.d.val))], s.signed ++ [(x, R, s.key.pow Y s.key.d.val)], s.bad⟩,
          (R, s.key.pow Y s.key.d.val)) := fun Y => by simp [Lazy.signLibrary, hp]
      simp only [Function.comp_def, hs, fTransform_fTransform]
      rw [Lazy.oracle_eq_bindK hp (fun Y => some (s.key.pow Y s.key.d.val)), bindK_bindK]
      refine bindK_congr fun Y _ => ?_
      rw [fTransform_eq_bindK]
      refine bindK_congr fun ROs hROs => ?_
      rw [Lazy.eq_of_mem_support_oracle hROs (p := (x, R))
        (v := (Y, some (s.key.pow Y s.key.d.val))) (by simp [List.lookup_append, hp])]
  · obtain ⟨m, R, S⟩ := x
    simp only [Function.comp_def, SigFake.outcome_ver, SigFake.kernel_some]
    cases hp : s.H.lookup (m, R) with
    | some v =>
      rw [Lazy.stepOn_ver_some _ _ hp, bindK_single, one_smul, fTransform_fTransform,
        fTransform_eq_bindK]
      rfl
    | none =>
      rw [Lazy.stepOn_ver_none _ _ hp, bindK_fTransform, Lazy.oracle_eq_bindK hp (fun _ => none),
        bindK_bindK]
      refine bindK_congr fun Y _ => ?_
      simp only [Function.comp_def, fTransform_fTransform, Lazy.State.define]
      rw [fTransform_eq_bindK]
      rfl
  · obtain ⟨m, R⟩ := x
    simp only [Function.comp_def, SigFake.outcome_ro, SigFake.kernel_some]
    cases hp : s.H.lookup (m, R) with
    | some v =>
      rw [Lazy.stepOn_ro_some _ _ hp, bindK_single, one_smul, fTransform_fTransform,
        fTransform_eq_bindK]
      refine bindK_congr fun ROs hROs => ?_
      rw [Lazy.eq_of_mem_support_oracle hROs hp]
      rfl
    | none =>
      rw [Lazy.stepOn_ro_none _ _ hp, bindK_fTransform, Lazy.oracle_eq_bindK hp (fun _ => none),
        bindK_bindK]
      refine bindK_congr fun Y _ => ?_
      simp only [Function.comp_def, fTransform_fTransform, Lazy.State.define]
      rw [fTransform_eq_bindK]
      refine bindK_congr fun ROs hROs => ?_
      rw [Lazy.eq_of_mem_support_oracle hROs (p := (m, R)) (v := (Y, none))
        (by simp [List.lookup_append, hp])]

/-- **`sig-fake` with the oracle sampled lazily**: the library is the lazy automaton with the
signing of the libraries and the verification by `𝒮`. -/
lemma SigFake.perPort_eq_lazy :
    SigFake.perPort Salt M keyGen (budget := q) = Resource.ofProbAutomaton _
      (Lazy.step keyGen Lazy.signLibrary Lazy.verifyFake) (Distribution.ProbDist.single none) := by
  rw [SigFake.perPort_eq_fresh]
  refine (Resource.ofProbAutomaton_eq_of_simulation (T := SigRO.perPort bits Salt M q)
    (Lazy.step keyGen Lazy.signLibrary Lazy.verifyFake)
    (SigFake.freshStep Salt M keyGen) _ _ (SigFake.kernel Salt M) (fun _ _ => True)
    (fun _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) (fun _ s x _ _ => ?_) ?_).symm
  · cases s with
    | none =>
      refine Lazy.step_simulatesAt_none keyGen _ _ _ _ rfl (fun x => ?_)
        (fun key x => SigFake.simulatesAt_some Salt M keyGen _ x) x
      rw [SigFake.outcome_none]
      refine bindK_congr fun key _ => ?_
      rw [SigFake.kernel_some, bindK_fTransform]
      exact congrArg (bindK · _) (Lazy.oracle_nil key).symm
    | some s => exact SigFake.simulatesAt_some Salt M keyGen s x
  · change Finsupp.single _ 1 = bindK (Finsupp.single none 1) _
    rw [bindK_single, one_smul]
    rfl

/-! #### `sig-fake` as a converter on `sig-real+ro`

The converter `sig-fake` on `sig-real+ro` is `sig-fake` along the kernel that keeps the key, the
oracle and the recorded signatures, and samples the key and the oracle while `sig-real+ro` has not
read them, which happens only after verification queries alone. -/

/-- **The converter `sig-fake` on `sig-real+ro` sampling afresh**. -/
def SigFake.fakeROStep :
    ProbStep (Option (List (M × Salt × RSA.Residue bits)) × (Option (RSA.Key bits ×
      (RSA.Residue bits → M × Salt → RSA.Residue bits)) × (Unit × (Unit × Unit))))
      SigningRO.Port (SigRO.Input bits Salt M) (SigRO.Output bits Salt) :=
  (SignatureScheme.FakeRO.body (RSA.Residue bits × RSA.Residue bits) M (Salt × RSA.Residue bits)
    (M × Salt) (RSA.Residue bits)).probCombine (SigReal.freshStep Salt M keyGen)
    (SignatureScheme.FakeRO.bound_spec _ _ _ _ _)

/-- The converter `sig-fake` on `sig-real+ro` is the automaton sampling afresh. -/
lemma SigFake.fakeRO_eq_fresh :
    SignatureScheme.FakeRO.perPort _ _ _ _ _ • SigReal.Library.perPort Salt M keyGen (budget := q) =
      Resource.ofProbAutomaton _ (SigFake.fakeROStep Salt M keyGen)
        (Distribution.ProbDist.single (none, (none, ((), ((), ()))))) := by
  unfold SignatureScheme.FakeRO.perPort SignatureScheme.FakeRO.perPortProgram
  exact ((((FreshSampling.source (SigReal.Library.law1 Salt M keyGen) _).parallel
    ((FreshSampling.source (SigReal.Library.law2 Salt M keyGen) _).parallel
      (FreshSampling.source (SigReal.Library.law3 Salt M keyGen) _))).ofProgram none _ _
        _).ofPreservingProgram none _ _ _ _ _ _ _).eq_fresh

/-- **The kernel from the converter `sig-fake` on `sig-real+ro` to `sig-fake`**: the key, the
oracle and the recorded signatures, the key and the oracle sampled while `sig-real+ro` has not
read them. -/
def SigFake.fakeROKernel : Option (List (M × Salt × RSA.Residue bits)) × (Option (RSA.Key bits ×
      (RSA.Residue bits → M × Salt → RSA.Residue bits)) × (Unit × (Unit × Unit))) →
    Distribution.ProbDist (Option (RSA.Key bits × (RSA.Residue bits → M × Salt →
      RSA.Residue bits) × List (M × Salt × RSA.Residue bits)) × (Unit × (Unit × Unit)))
  | (s, (some (key, ROs), _)) => Distribution.ProbDist.single (some (key, ROs, s.getD []),
      ((), ((), ())))
  | (none, (none, _)) => Distribution.ProbDist.single (none, ((), ((), ())))
  | (some signed, (none, _)) => Distribution.ProbDist.bind keyGen fun key =>
      Distribution.ProbDist.map (fun ROs => (some (key, ROs, signed), ((), ((), ()))))
        (residueOracles (bits := bits) (M × Salt))

omit [Nonempty Salt] in
/-- The kernel once `sig-real+ro` has read the key and the oracle. -/
lemma SigFake.fakeROKernel_some (sF : Option (List (M × Salt × RSA.Residue bits)))
    (key : RSA.Key bits) (ROs : RSA.Residue bits → M × Salt → RSA.Residue bits)
    (r : Unit × (Unit × Unit)) :
    (SigFake.fakeROKernel Salt M keyGen (sF, (some (key, ROs), r))).1 =
      Finsupp.single (some (key, ROs, sF.getD []), ((), ((), ()))) 1 := rfl

/-- **Once `sig-real+ro` has read the key and the oracle**, the converter `sig-fake` on it steps
as `sig-fake` with the signatures it recorded. -/
lemma SigFake.fakeRO_outcome_some (sF : Option (List (M × Salt × RSA.Residue bits)))
    (key : RSA.Key bits) (ROs : RSA.Residue bits → M × Salt → RSA.Residue bits)
    (x : Σ i, SigRO.Input bits Salt M i) :
    (SigFake.freshStep Salt M keyGen).outcome (some (key, ROs, sF.getD []), ((), ((), ()))) x =
      bindK ((SigFake.fakeROStep Salt M keyGen).outcome (sF, (some (key, ROs), ((), ((), ())))) x)
        fun p => fTransform (fun s₂ => (s₂, p.2)) (SigFake.fakeROKernel Salt M keyGen p.1).1 := by
  obtain ⟨_ | _ | _ | _, x⟩ := x
  · rw [SigFake.outcome_pk, SigFake.fakeROStep, SignatureScheme.FakeRO.outcome_pk,
      SigReal.outcome_pk]
    simp only [fTransform_single, bindK_single, one_smul, SigFake.fakeROKernel_some,
      Option.getD_some]
  · rw [SigFake.outcome_sign, SigFake.fakeROStep, SignatureScheme.FakeRO.outcome_sign,
      SigReal.outcome_sign, fTransform_bindK, bindK_bindK]
    refine bindK_congr fun R _ => ?_
    simp only [fTransform_single, bindK_single, one_smul, SigFake.fakeROKernel_some,
      Option.getD_some]
  · obtain ⟨m, R, S⟩ := x
    rw [SigFake.outcome_ver, SigFake.fakeROStep, SignatureScheme.FakeRO.outcome_ver]
    simp only [bindK_single, one_smul, SigFake.fakeROKernel_some, Option.getD_some,
      fTransform_single]
    congr
  · obtain ⟨m, R⟩ := x
    rw [SigFake.outcome_ro, SigFake.fakeROStep, SignatureScheme.FakeRO.outcome_ro,
      SigReal.outcome_ro]
    simp only [fTransform_single, bindK_single, one_smul, SigFake.fakeROKernel_some,
      Option.getD_some]

/-- **Before `sig-real+ro` has read the key and the oracle**, the converter `sig-fake` on it
answers a query other than a verification as once they are sampled. -/
lemma SigFake.fakeRO_outcome_none (sF : Option (List (M × Salt × RSA.Residue bits)))
    (x : Σ i, SigRO.Input bits Salt M i) (hx : x.1 ≠ .ver) :
    (SigFake.fakeROStep Salt M keyGen).outcome (sF, (none, ((), ((), ())))) x =
      bindK keyGen.1 fun key => bindK (residueOracles (bits := bits) (M × Salt)).1 fun ROs =>
        (SigFake.fakeROStep Salt M keyGen).outcome (sF, (some (key, ROs), ((), ((), ())))) x := by
  obtain ⟨_ | _ | _ | _, x⟩ := x
  · rw [SigFake.fakeROStep, SignatureScheme.FakeRO.outcome_pk, SigReal.outcome_none,
      fTransform_bindK]
    refine bindK_congr fun key _ => ?_
    rw [fTransform_bindK]
    refine bindK_congr fun ROs _ => ?_
    rw [SignatureScheme.FakeRO.outcome_pk]
  · rw [SigFake.fakeROStep, SignatureScheme.FakeRO.outcome_sign, SigReal.outcome_none,
      fTransform_bindK]
    refine bindK_congr fun key _ => ?_
    rw [fTransform_bindK]
    refine bindK_congr fun ROs _ => ?_
    rw [SignatureScheme.FakeRO.outcome_sign]
  · exact absurd rfl hx
  · rw [SigFake.fakeROStep, SignatureScheme.FakeRO.outcome_ro, SigReal.outcome_none,
      fTransform_bindK]
    refine bindK_congr fun key _ => ?_
    rw [fTransform_bindK]
    refine bindK_congr fun ROs _ => ?_
    rw [SignatureScheme.FakeRO.outcome_ro]

/-- **`sig-fake` is the converter `sig-fake` on `sig-real+ro`** [1, §8.2]. -/
theorem SigFake.perPort_eq_fakeRO :
    SigFake.perPort Salt M keyGen (budget := q) =
      SignatureScheme.FakeRO.perPort _ _ _ _ _ • SigReal Salt M keyGen q := by
  rw [SigReal.eq_library, SigFake.perPort_eq_fresh, SigFake.fakeRO_eq_fresh]
  refine (Resource.ofProbAutomaton_eq_of_simulation (T := SigRO.perPort bits Salt M q)
    (SigFake.fakeROStep Salt M keyGen) (SigFake.freshStep Salt M keyGen) _ _
    (SigFake.fakeROKernel Salt M keyGen) (fun _ _ => True) (fun _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial) (fun _ s x _ _ => ?_) ?_).symm
  · obtain ⟨sF, sR, ⟨⟩, ⟨⟩, ⟨⟩⟩ := s
    unfold ProbStep.SimulatesAt
    rcases sR with _ | ⟨key, ROs⟩
    · -- Before the key and the oracle are read: the kernel samples them, as `sig-fake` does.
      have hK : ∀ signed : List (M × Salt × RSA.Residue bits),
          (SigFake.fakeROKernel Salt M keyGen (some signed, (none, ((), ((), ()))))).1 =
            bindK keyGen.1 fun key => fTransform (fun ROs => (some (key, ROs, signed),
              ((), ((), ())))) (residueOracles (bits := bits) (M × Salt)).1 := fun _ =>
        Distribution.ProbDist.bind_val _ _
      have hLHS : bindK (SigFake.fakeROKernel Salt M keyGen (sF, (none, ((), ((), ()))))).1
          (fun s₂ => (SigFake.freshStep Salt M keyGen).outcome s₂ x) =
          bindK keyGen.1 fun key => bindK (residueOracles (bits := bits) (M × Salt)).1 fun ROs =>
            (SigFake.freshStep Salt M keyGen).outcome
              (some (key, ROs, sF.getD []), ((), ((), ()))) x := by
        rcases sF with _ | signed
        · rw [show (SigFake.fakeROKernel Salt M keyGen (none, (none, ((), ((), ()))))).1 =
              Finsupp.single (none, ((), ((), ()))) 1 from rfl, bindK_single, one_smul,
            SigFake.outcome_none]
          rfl
        · rw [hK, bindK_bindK]
          refine bindK_congr fun key _ => ?_
          rw [bindK_fTransform]
          rfl
      rw [hLHS]
      by_cases hx : x.1 = .ver
      · obtain ⟨i, x⟩ := x
        dsimp only at hx
        subst hx
        obtain ⟨m, R, S⟩ := x
        rw [SigFake.fakeROStep, SignatureScheme.FakeRO.outcome_ver, bindK_single, one_smul, hK,
          fTransform_bindK]
        refine bindK_congr fun key _ => ?_
        rw [fTransform_fTransform, fTransform_eq_bindK]
        refine bindK_congr fun ROs _ => ?_
        rw [SigFake.outcome_ver]
        congr
      · rw [SigFake.fakeRO_outcome_none _ _ _ _ _ hx, bindK_bindK]
        refine bindK_congr fun key _ => ?_
        rw [bindK_bindK]
        refine bindK_congr fun ROs _ => ?_
        rw [SigFake.fakeRO_outcome_some]
    · rw [SigFake.fakeROKernel_some, bindK_single, one_smul, SigFake.fakeRO_outcome_some]
  · change Finsupp.single _ 1 = bindK (Finsupp.single _ 1) _
    rw [bindK_single, one_smul]
    rfl

end Libraries

/-! ### The reduction as the lazy automaton -/

section ReductionAutomaton

open Probability.Distribution

section ManyChallenges

variable (keyGen : Distribution.ProbDist (RSA.Key bits))

/-- **`rsa*-real` sampling afresh**: its program against fresh samples of its laws. -/
def RSAStar.Real.freshStep :
    ProbStep (Option (RSA.Key bits × List (RSA.Residue bits)) × (Unit × Unit)) RSAStar.Port
      (RSAStar.Input bits) (RSAStar.Output bits) :=
  (RSAStar.Real.body keyGen).probCombine (ProbStep.parallel
    (ProbStep.fresh (RSAStar.Real.law1 keyGen)) (ProbStep.fresh (RSAStar.Real.law2 keyGen)))
    (RSAStar.Real.bound_spec keyGen)

/-- **`rsa*-fake` sampling afresh**: its program against fresh samples of its laws. -/
def RSAStar.Fake.freshStep :
    ProbStep (Option (RSA.Key bits) × (Unit × Unit)) RSAStar.Port (RSAStar.Input bits)
      (RSAStar.Output bits) :=
  (RSAStar.Fake.body keyGen).probCombine (ProbStep.parallel
    (ProbStep.fresh (RSAStar.Fake.law1 keyGen)) (ProbStep.fresh (RSAStar.Fake.law2 keyGen)))
    (RSAStar.Fake.bound_spec keyGen)

/-- `rsa*-real` as fresh sampling. -/
def RSAStar.Real.freshSampling (q : RSAStar.Port → ℕ) :
    FreshSampling (RSAStar.perPort bits q) (RSAStar.Real.perPort keyGen) :=
  ((FreshSampling.source (RSAStar.Real.law1 keyGen) _).parallel
    (FreshSampling.source (RSAStar.Real.law2 keyGen) _)).ofProgram none _ _ _

/-- `rsa*-fake` as fresh sampling. -/
def RSAStar.Fake.freshSampling (q : RSAStar.Port → ℕ) :
    FreshSampling (RSAStar.perPort bits q) (RSAStar.Fake.perPort keyGen) :=
  ((FreshSampling.source (RSAStar.Fake.law1 keyGen) _).parallel
    (FreshSampling.source (RSAStar.Fake.law2 keyGen) _)).ofProgram none _ _ _

/-- `pk*()` in `rsa*-real`, sampled afresh: `(N, e)`. -/
lemma RSAStar.Real.outcome_pk (key : RSA.Key bits) (chal : List (RSA.Residue bits)) :
    (RSAStar.Real.freshStep keyGen).outcome (some (key, chal), ((), ())) ⟨.pk, ()⟩ =
      Finsupp.single ((some (key, chal), ((), ())),
        (⟨.pk, (key.N, key.e)⟩ : Σ i, RSAStar.Output bits i)) 1 := by
  rw [RSAStar.Real.freshStep, ProbStep.outcome, Program.probCombine_val]
  fresh_return RSAStar.Real.body RSAStar.Port.pk (some (key, chal), (key.N, key.e))

/-- `challenge*()` in `rsa*-real`, sampled afresh: a uniform residue `Y`, added to `𝒴`. -/
lemma RSAStar.Real.outcome_challenge (key : RSA.Key bits) (chal : List (RSA.Residue bits)) :
    (RSAStar.Real.freshStep keyGen).outcome (some (key, chal), ((), ())) ⟨.challenge, ()⟩ =
      bindK (RSA.residue key.N).1 fun Y => Finsupp.single ((some (key, chal ++ [Y]), ((), ())),
        (⟨.challenge, Y⟩ : Σ i, RSAStar.Output bits i)) 1 := by
  rw [RSAStar.Real.freshStep, ProbStep.outcome, Program.probCombine_val,
    show RSAStar.Real.bound keyGen = 1 + 1 from rfl]
  fresh_call RSAStar.Real.body ⟨.inr (), ()⟩
  rw [← RSA.fTransform_eval_residues, bindK_fTransform]
  refine bindK_congr fun Ys _ => ?_
  fresh_return RSAStar.Real.body RSAStar.Port.challenge (some (key, chal ++ [Ys key.N]), Ys key.N)

/-- `check*(X)` in `rsa*-real`, sampled afresh: whether `X^e mod N ∈ 𝒴`. -/
lemma RSAStar.Real.outcome_check (key : RSA.Key bits) (chal : List (RSA.Residue bits))
    (X : RSA.Residue bits) :
    (RSAStar.Real.freshStep keyGen).outcome (some (key, chal), ((), ())) ⟨.check, X⟩ =
      Finsupp.single ((some (key, chal), ((), ())),
        (⟨.check, decide (key.pow X key.e.val ∈ chal)⟩ : Σ i, RSAStar.Output bits i)) 1 := by
  rw [RSAStar.Real.freshStep, ProbStep.outcome, Program.probCombine_val]
  fresh_return RSAStar.Real.body RSAStar.Port.check
    (some (key, chal), decide (key.pow X key.e.val ∈ chal))

/-- The first `pk*()` of `rsa*-real`, sampled afresh: it samples the key. -/
lemma RSAStar.Real.outcome_none_pk :
    (RSAStar.Real.freshStep keyGen).outcome (none, ((), ())) ⟨.pk, ()⟩ =
      bindK keyGen.1 fun key => Finsupp.single ((some (key, []), ((), ())),
        (⟨.pk, (key.N, key.e)⟩ : Σ i, RSAStar.Output bits i)) 1 := by
  rw [RSAStar.Real.freshStep, ProbStep.outcome, Program.probCombine_val,
    show RSAStar.Real.bound keyGen = 1 + 1 from rfl]
  fresh_call RSAStar.Real.body ⟨.inl (), ()⟩
  refine bindK_congr fun key _ => ?_
  fresh_return RSAStar.Real.body RSAStar.Port.pk
    (some (key, []), (RSA.Key.N key, RSA.Key.e key))

/-- `pk*()` in `rsa*-fake`, sampled afresh: `(N, e)`. -/
lemma RSAStar.Fake.outcome_pk (key : RSA.Key bits) :
    (RSAStar.Fake.freshStep keyGen).outcome (some key, ((), ())) ⟨.pk, ()⟩ =
      Finsupp.single ((some key, ((), ())),
        (⟨.pk, (key.N, key.e)⟩ : Σ i, RSAStar.Output bits i)) 1 := by
  rw [RSAStar.Fake.freshStep, ProbStep.outcome, Program.probCombine_val]
  fresh_return RSAStar.Fake.body RSAStar.Port.pk (some key, (key.N, key.e))

/-- `challenge*()` in `rsa*-fake`, sampled afresh: a uniform residue `Y`. -/
lemma RSAStar.Fake.outcome_challenge (key : RSA.Key bits) :
    (RSAStar.Fake.freshStep keyGen).outcome (some key, ((), ())) ⟨.challenge, ()⟩ =
      bindK (RSA.residue key.N).1 fun Y => Finsupp.single ((some key, ((), ())),
        (⟨.challenge, Y⟩ : Σ i, RSAStar.Output bits i)) 1 := by
  rw [RSAStar.Fake.freshStep, ProbStep.outcome, Program.probCombine_val,
    show RSAStar.Fake.bound keyGen = 1 + 1 from rfl]
  fresh_call RSAStar.Fake.body ⟨.inr (), ()⟩
  rw [← RSA.fTransform_eval_residues, bindK_fTransform]
  refine bindK_congr fun Ys _ => ?_
  fresh_return RSAStar.Fake.body RSAStar.Port.challenge (some key, Ys key.N)

/-- `check*(X)` in `rsa*-fake`, sampled afresh: `false`. -/
lemma RSAStar.Fake.outcome_check (key : RSA.Key bits) (X : RSA.Residue bits) :
    (RSAStar.Fake.freshStep keyGen).outcome (some key, ((), ())) ⟨.check, X⟩ =
      Finsupp.single ((some key, ((), ())),
        (⟨.check, false⟩ : Σ i, RSAStar.Output bits i)) 1 := by
  rw [RSAStar.Fake.freshStep, ProbStep.outcome, Program.probCombine_val]
  fresh_return RSAStar.Fake.body RSAStar.Port.check (some key, false)

/-- The first `pk*()` of `rsa*-fake`, sampled afresh: it samples the key. -/
lemma RSAStar.Fake.outcome_none_pk :
    (RSAStar.Fake.freshStep keyGen).outcome (none, ((), ())) ⟨.pk, ()⟩ =
      bindK keyGen.1 fun key => Finsupp.single ((some key, ((), ())),
        (⟨.pk, (key.N, key.e)⟩ : Σ i, RSAStar.Output bits i)) 1 := by
  rw [RSAStar.Fake.freshStep, ProbStep.outcome, Program.probCombine_val,
    show RSAStar.Fake.bound keyGen = 1 + 1 from rfl]
  fresh_call RSAStar.Fake.body ⟨.inl (), ()⟩
  refine bindK_congr fun key _ => ?_
  fresh_return RSAStar.Fake.body RSAStar.Port.pk (some key, (RSA.Key.N key, RSA.Key.e key))

end ManyChallenges

section Reduction

variable (Salt : Type) [Fintype Salt] [Nonempty Salt] [DecidableEq Salt]
  (M : Type) [Fintype M] [DecidableEq M]

/-- **`𝓡` sampling afresh** on the inside step `stepR`: its program against `stepR` beside
fresh samples of its laws. -/
def 𝓡.freshStep {R : Type}
    (stepR : ProbStep R RSAStar.Port (RSAStar.Input bits) (RSAStar.Output bits)) :
    ProbStep (Option (List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits))) ×
      (R × (Unit × Unit))) SigningRO.Port (SigRO.Input bits Salt M) (SigRO.Output bits Salt) :=
  (𝓡.body bits Salt M).probCombine (ProbStep.parallel stepR (ProbStep.parallel
    (ProbStep.fresh (𝓡.law1 bits Salt M)) (ProbStep.fresh (𝓡.law2 bits Salt M))))
    (𝓡.bound_spec bits Salt M)

/-- `𝓡` on a resource presented as fresh sampling, as fresh sampling. -/
def 𝓡.freshSampling (q : SigningRO.Port → ℕ) {R₀ : Resource (RSAStar.perPort bits (insideBudget q))}
    (Φ : FreshSampling (RSAStar.perPort bits (insideBudget q)) R₀) :
    FreshSampling (SigRO.perPort bits Salt M q) (𝓡.perLabel Salt M q • R₀) :=
  have Ψ : FreshSampling (𝓡.inside bits Salt M q)
      (Interface.parallel R₀ (𝓡.randomness bits Salt M (𝓡.bound bits Salt M * ∑ i, q i))) :=
    Φ.parallel ((FreshSampling.source (𝓡.law1 bits Salt M) _).parallel
      (FreshSampling.source (𝓡.law2 bits Salt M) _))
  FreshSampling.ofRightContext
    (Converter.ofLabelBoundedProgram (A := SigRO.perPort bits Salt M q)
      (B := 𝓡.inside bits Salt M q) none (𝓡.body bits Salt M) (𝓡.bound_spec bits Salt M)
      𝓡.calls (𝓡.labelBounded Salt M) q (fun _ hd => hd.2) (𝓡.admits Salt M q))
    (Ψ.ofLabelBoundedProgram (A := SigRO.perPort bits Salt M q) none (𝓡.body bits Salt M)
      (𝓡.bound_spec bits Salt M) 𝓡.calls (𝓡.labelBounded Salt M) q (fun _ hd => hd.2)
      (𝓡.admits Salt M q))

/-- The state of `𝓡` from a lazy state: its table `H`, and the state `ρ key H` of the
inside library; before the first query, nothing stored and the library at `r₀`. -/
def 𝓡.stateOf {R : Type}
    (ρ : RSA.Key bits → List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits)) → R)
    (r₀ : R) : Option (Lazy.State bits Salt M) →
      Option (List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits))) ×
        (R × (Unit × Unit))
  | none => (none, (r₀, ((), ())))
  | some s => (some s.H, (ρ s.key s.H, ((), ())))

variable {R : Type} (stepR : ProbStep R RSAStar.Port (RSAStar.Input bits) (RSAStar.Output bits))
  (ρ : RSA.Key bits → List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits)) → R)
  (r₀ : R) (keyGen : Distribution.ProbDist (RSA.Key bits))
  (chk : RSA.Key bits → List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits)) →
    RSA.Residue bits → Bool)

/-- **A step of `𝓡` on a library answering as the model `ρ`**: from a state whose `pk*()` gives
keys distributed as `μ`, the library then at `ρ key H`, a step of `𝓡` is the image under
`𝓡.stateOf` of a step of the lazy automaton with the signing and verification of the
reduction. -/
lemma 𝓡.outcome_some
    (hch : ∀ key L p, stepR.outcome (ρ key L) ⟨.challenge, ()⟩ =
      bindK (RSA.residue key.N).1 fun Y => Finsupp.single (ρ key (L ++ [(p, Y, none)]),
        (⟨.challenge, Y⟩ : Σ i, RSAStar.Output bits i)) 1)
    (hck : ∀ key L S, stepR.outcome (ρ key L) ⟨.check, S⟩ =
      Finsupp.single (ρ key L, (⟨.check, chk key L S⟩ : Σ i, RSAStar.Output bits i)) 1)
    (hprog : ∀ key L p Y S, ρ key (L ++ [(p, Y, some S)]) = ρ key L)
    (L : List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits))) (r : R)
    (μ : Distribution (RSA.Key bits))
    (hpk : stepR.outcome r ⟨.pk, ()⟩ = bindK μ fun key =>
      Finsupp.single (ρ key L, (⟨.pk, (key.N, key.e)⟩ : Σ i, RSAStar.Output bits i)) 1)
    (Sg : List (M × Salt × RSA.Residue bits)) (b : Bool)
    (x : Σ i, SigRO.Input bits Salt M i) :
    (𝓡.freshStep Salt M stepR).outcome (some L, (r, ((), ()))) x =
      bindK μ fun key => fTransform (Prod.map (𝓡.stateOf Salt M ρ r₀) id)
        ((Lazy.step keyGen Lazy.signReduction (Lazy.verifyReduction chk)).outcome
          (some ⟨key, L, Sg, b⟩) x) := by
  simp only [Lazy.step_outcome_some, fTransform_fTransform]
  obtain ⟨_ | _ | _ | _, x⟩ := x
  · cases x
    dsimp only [𝓡.freshStep]
    rw [ProbStep.outcome, Program.probCombine_val, show 𝓡.bound bits Salt M = 2 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl .pk, ()⟩) (by simp [𝓡.body, callProg]),
      ProbStep.outcome_parallel_inl, hpk]
    simp only [bindK_fTransform,
      Function.comp_def, fTransform_bindK, bindK_bindK, bindK_single, one_smul]
    refine bindK_congr fun key _ => ?_
    rw [Program.probInvoke_inl (a := (some L, (key.N, key.e)))
      (by simp [𝓡.body, callProg, returnProg, ProbStep.inlReply]), Lazy.stepOn_pk,
      fTransform_single, fTransform_single]
    rfl
  · dsimp only [𝓡.freshStep]
    rw [ProbStep.outcome, Program.probCombine_val, show 𝓡.bound bits Salt M = 2 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl .pk, ()⟩) (by simp [𝓡.body, callProg]),
      ProbStep.outcome_parallel_inl, hpk]
    simp only [bindK_fTransform, Function.comp_def, fTransform_bindK, bindK_bindK, bindK_single,
      one_smul]
    refine bindK_congr fun key _ => ?_
    rw [Program.probInvoke_succ_inr (q := ⟨.inr (.inl ()), ()⟩)
        (by simp [𝓡.body, callProg, ProbStep.inlReply]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inl, Lazy.stepOn_sign,
      fTransform_bindK]
    simp only [ProbStep.outcome, ProbStep.fresh, fTransform_fTransform, bindK_fTransform,
      Function.comp_def, fTransform_bindK]
    refine bindK_congr fun R _ => ?_
    rw [Program.probInvoke_succ_inr (q := ⟨.inr (.inr ()), ()⟩)
        (by simp [𝓡.body, callProg, ProbStep.inlReply, ProbStep.inrReply, ProbStep.tagged]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, fTransform_fTransform, bindK_fTransform,
      Function.comp_def, fTransform_bindK]
    rw [← RSA.fTransform_eval_residues, fTransform_fTransform, fTransform_eq_bindK]
    change bindK (RSA.residues (bits := bits)).1 _ = bindK (RSA.residues (bits := bits)).1 _
    refine bindK_congr fun Ss _ => ?_
    cases hp : L.lookup (x, R) with
    | none =>
      rw [Program.probInvoke_inl (a := (some (L ++ [((x, R), RSA.powMod key.N key.e (Ss key.N),
          some (Ss key.N))]), (R, Ss key.N)))
        (by simp [𝓡.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply,
          ProbStep.tagged, hp])]
      simp [fTransform, ProbStep.tagged, Lazy.signReduction, hp, 𝓡.stateOf, hprog,
        RSA.powMod_eq_pow]
    | some v =>
      obtain ⟨Y, _ | S₀⟩ := v
      · rw [Program.probInvoke_inl (a := (some L, (R, Ss key.N)))
          (by simp [𝓡.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply,
            ProbStep.tagged, hp])]
        simp [fTransform, ProbStep.tagged, Lazy.signReduction, hp, 𝓡.stateOf]
      · rw [Program.probInvoke_inl (a := (some L, (R, S₀)))
          (by simp [𝓡.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply,
            ProbStep.tagged, hp])]
        simp [fTransform, ProbStep.tagged, Lazy.signReduction, hp, 𝓡.stateOf]
  · obtain ⟨m, R, S⟩ := x
    dsimp only [𝓡.freshStep]
    rw [ProbStep.outcome, Program.probCombine_val, show 𝓡.bound bits Salt M = 2 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl .pk, ()⟩) (by simp [𝓡.body, callProg]),
      ProbStep.outcome_parallel_inl, hpk]
    simp only [bindK_fTransform, Function.comp_def, fTransform_bindK, bindK_bindK, bindK_single,
      one_smul]
    refine bindK_congr fun key _ => ?_
    cases hp : L.lookup (m, R) with
    | some v =>
      obtain ⟨Y, _ | S₀⟩ := v
      · rw [Lazy.stepOn_ver_some (s := ⟨key, L, Sg, b⟩) _ _ hp S, fTransform_single]
        by_cases hg : S < key.N ∧ Y = key.pow S key.e.val
        · rw [Program.probInvoke_succ_inr (q := ⟨.inl .check, S⟩)
              (by simp [𝓡.body, callProg, ProbStep.inlReply, hp, hg, RSA.powMod_eq_pow]),
            ProbStep.outcome_parallel_inl, hck]
          simp only [bindK_single,
            one_smul, fTransform_single]
          rw [Program.probInvoke_inl (a := (some L, chk key L S))
            (by simp [𝓡.body, callProg, returnProg, ProbStep.inlReply, hp, hg,
              RSA.powMod_eq_pow])]
          simp [fTransform, ProbStep.tagged, Lazy.verifyReduction, hg, 𝓡.stateOf]
        · rw [Program.probInvoke_inl (a := (some L, false))
            (by simp [𝓡.body, callProg, returnProg, ProbStep.inlReply, hp, hg,
              RSA.powMod_eq_pow])]
          simp [fTransform, ProbStep.tagged, Lazy.verifyReduction, hg, 𝓡.stateOf]
      · rw [Lazy.stepOn_ver_some (s := ⟨key, L, Sg, b⟩) _ _ hp S, fTransform_single,
          Program.probInvoke_inl
            (a := (some L, decide (S.val < key.N.val ∧ Y = RSA.powMod key.N key.e S)))
            (by simp [𝓡.body, callProg, returnProg, ProbStep.inlReply, hp])]
        simp [fTransform, ProbStep.tagged, Lazy.verifyReduction, 𝓡.stateOf, RSA.powMod_eq_pow]
    | none =>
      rw [Lazy.stepOn_ver_none (s := ⟨key, L, Sg, b⟩) _ _ hp S,
        Program.probInvoke_succ_inr (q := ⟨.inl .challenge, ()⟩)
          (by simp [𝓡.body, callProg, ProbStep.inlReply, hp]),
        ProbStep.outcome_parallel_inl, hch key L (m, R)]
      simp only [fTransform_bindK, bindK_bindK,
        bindK_single, one_smul, fTransform_single]
      rw [fTransform_fTransform, fTransform_eq_bindK]
      refine bindK_congr fun Y _ => ?_
      by_cases hg : S < key.N ∧ Y = key.pow S key.e.val
      · rw [Program.probInvoke_succ_inr (q := ⟨.inl .check, S⟩)
            (by simp [𝓡.body, callProg, ProbStep.inlReply, hp, hg, RSA.powMod_eq_pow]),
          ProbStep.outcome_parallel_inl, hck]
        simp only [Function.comp_def, bindK_single,
          one_smul, fTransform_single]
        rw [Program.probInvoke_inl
          (a := (some (L ++ [((m, R), Y, none)]), chk key (L ++ [((m, R), Y, none)]) S))
          (by simp [𝓡.body, callProg, returnProg, ProbStep.inlReply, hp, hg,
            RSA.powMod_eq_pow])]
        simp [fTransform, ProbStep.tagged, Lazy.verifyReduction, Lazy.State.define, hg, 𝓡.stateOf]
      · rw [Program.probInvoke_inl (a := (some (L ++ [((m, R), Y, none)]), false))
          (by simp [𝓡.body, callProg, returnProg, ProbStep.inlReply, hp, hg,
            RSA.powMod_eq_pow])]
        simp [fTransform, ProbStep.tagged, 𝓡.stateOf, Lazy.verifyReduction, Lazy.State.define]
        rcases not_and_or.mp hg with h | h <;> simp [h]
  · obtain ⟨m, R⟩ := x
    dsimp only [𝓡.freshStep]
    rw [ProbStep.outcome, Program.probCombine_val, show 𝓡.bound bits Salt M = 2 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl .pk, ()⟩) (by simp [𝓡.body, callProg]),
      ProbStep.outcome_parallel_inl, hpk]
    simp only [bindK_fTransform, Function.comp_def, fTransform_bindK, bindK_bindK, bindK_single,
      one_smul]
    refine bindK_congr fun key _ => ?_
    cases hp : L.lookup (m, R) with
    | some v =>
      rw [Lazy.stepOn_ro_some (s := ⟨key, L, Sg, b⟩) _ _ hp, fTransform_single,
        Program.probInvoke_inl (o := SigningRO.Port.ro) (a := (some L, v.1))
          (by simp [𝓡.body, callProg, returnProg, ProbStep.inlReply, hp])]
      simp [fTransform, ProbStep.tagged, 𝓡.stateOf]
    | none =>
      rw [Lazy.stepOn_ro_none (s := ⟨key, L, Sg, b⟩) _ _ hp,
        Program.probInvoke_succ_inr (q := ⟨.inl .challenge, ()⟩)
          (by simp [𝓡.body, callProg, ProbStep.inlReply, hp]),
        ProbStep.outcome_parallel_inl, hch key L (m, R)]
      simp only [fTransform_bindK, bindK_bindK,
        bindK_single, one_smul, fTransform_single]
      rw [fTransform_fTransform, fTransform_eq_bindK]
      refine bindK_congr fun Y _ => ?_
      rw [Program.probInvoke_inl (o := SigningRO.Port.ro)
        (a := (some (L ++ [((m, R), Y, none)]), Y))
        (by simp [𝓡.body, callProg, returnProg, ProbStep.inlReply, hp])]
      simp [fTransform, ProbStep.tagged, 𝓡.stateOf, Lazy.State.define]

/-- Before the first query, `𝓡` steps as with nothing defined. -/
lemma 𝓡.outcome_none (rr : R × (Unit × Unit)) (x : Σ i, SigRO.Input bits Salt M i) :
    (𝓡.freshStep Salt M stepR).outcome (none, rr) x =
      (𝓡.freshStep Salt M stepR).outcome (some [], rr) x := by
  have hP : 𝓡.body bits Salt M none = 𝓡.body bits Salt M (some []) := by
    funext i u h
    cases i <;> rfl
  have hinv : ∀ n r h, (𝓡.body bits Salt M).probInvoke (ProbStep.parallel stepR
      (ProbStep.parallel (ProbStep.fresh (𝓡.law1 bits Salt M))
        (ProbStep.fresh (𝓡.law2 bits Salt M)))) none x.1 x.2 n r h =
      (𝓡.body bits Salt M).probInvoke (ProbStep.parallel stepR
        (ProbStep.parallel (ProbStep.fresh (𝓡.law1 bits Salt M))
          (ProbStep.fresh (𝓡.law2 bits Salt M)))) (some []) x.1 x.2 n r h := by
    intro n
    induction n with
    | zero => intro r h; simp only [Program.probInvoke, hP]
    | succ n ih => intro r h; simp only [Program.probInvoke, hP, ih]
  simp only [𝓡.freshStep, ProbStep.outcome, Program.probCombine_val]
  rw [hinv]

/-- **`𝓡` on a library that answers as the model `ρ`**: if the inside step answers `pk*()` with
the key and `check*(S)` with `chk` from the states `ρ key table`, samples a uniform challenge
recorded at a new point, and samples the key at its first query, the automaton of `𝓡` on it is
the lazy automaton with the signing and verification of the reduction. -/
lemma 𝓡.ofProbAutomaton_eq (q : SigningRO.Port → ℕ)
    (hpk : ∀ key L, stepR.outcome (ρ key L) ⟨.pk, ()⟩ =
      Finsupp.single (ρ key L, (⟨.pk, (key.N, key.e)⟩ : Σ i, RSAStar.Output bits i)) 1)
    (hch : ∀ key L p, stepR.outcome (ρ key L) ⟨.challenge, ()⟩ =
      bindK (RSA.residue key.N).1 fun Y => Finsupp.single (ρ key (L ++ [(p, Y, none)]),
        (⟨.challenge, Y⟩ : Σ i, RSAStar.Output bits i)) 1)
    (hck : ∀ key L S, stepR.outcome (ρ key L) ⟨.check, S⟩ =
      Finsupp.single (ρ key L, (⟨.check, chk key L S⟩ : Σ i, RSAStar.Output bits i)) 1)
    (hprog : ∀ key L p Y S, ρ key (L ++ [(p, Y, some S)]) = ρ key L)
    (h₀ : stepR.outcome r₀ ⟨.pk, ()⟩ = bindK keyGen.1 fun key =>
      Finsupp.single (ρ key [], (⟨.pk, (key.N, key.e)⟩ : Σ i, RSAStar.Output bits i)) 1) :
    Resource.ofProbAutomaton (SigRO.perPort bits Salt M q)
        (Lazy.step keyGen Lazy.signReduction (Lazy.verifyReduction chk))
        (Distribution.ProbDist.single none) =
      Resource.ofProbAutomaton _ (𝓡.freshStep Salt M stepR)
        (Distribution.ProbDist.single (none, (r₀, ((), ())))) := by
  refine Resource.ofProbAutomaton_eq_of_map _ _ _ _ (𝓡.stateOf Salt M ρ r₀) (fun s x => ?_) ?_
  · cases s with
    | none =>
      rw [𝓡.stateOf, 𝓡.outcome_none, 𝓡.outcome_some Salt M stepR ρ r₀ keyGen chk hch hck hprog
        [] r₀ keyGen.1 h₀ [] false, Lazy.step_outcome_none, fTransform_bindK]
    | some s =>
      rw [𝓡.stateOf, 𝓡.outcome_some Salt M stepR ρ r₀ keyGen chk hch hck hprog s.H
        (ρ s.key s.H) (Finsupp.single s.key 1) (by rw [hpk, bindK_single, one_smul]) s.signed
        s.bad, bindK_single, one_smul]
  · exact (fTransform_single (𝓡.stateOf Salt M ρ r₀) none 1).symm

end Reduction

section Instances

variable (Salt : Type) [Fintype Salt] [Nonempty Salt] [DecidableEq Salt]
  (M : Type) [Fintype M] [DecidableEq M]
  (keyGen : Distribution.ProbDist (RSA.Key bits)) (q : SigningRO.Port → ℕ)

/-- **The reduction on `rsa*-real`** is the lazy automaton with the signing of the reduction,
checking a root against the challenges. -/
lemma 𝓡.smul_real :
    𝓡.perLabel Salt M q • RSAStar.Real.perPort keyGen = Resource.ofProbAutomaton _
      (Lazy.step keyGen Lazy.signReduction (Lazy.verifyReduction fun key table S =>
        decide (key.pow S key.e.val ∈ Lazy.challenges table)))
      (Distribution.ProbDist.single none) :=
  (𝓡.freshSampling Salt M q (RSAStar.Real.freshSampling keyGen _)).eq_fresh.trans
    (𝓡.ofProbAutomaton_eq Salt M (RSAStar.Real.freshStep keyGen)
      (fun key table => (some (key, Lazy.challenges table), ((), ()))) (none, ((), ())) keyGen _ q
      (fun key table => RSAStar.Real.outcome_pk keyGen key _)
      (fun key table p => by
        rw [RSAStar.Real.outcome_challenge]
        simp only [Lazy.challenges_append_none])
      (fun key table S => RSAStar.Real.outcome_check keyGen key _ S)
      (fun key table p Y S => by simp only [Lazy.challenges_append_some])
      (RSAStar.Real.outcome_none_pk keyGen)).symm

/-- **The reduction on `rsa*-fake`** is the lazy automaton with the signing of the reduction,
rejecting every root. -/
lemma 𝓡.smul_fake :
    𝓡.perLabel Salt M q • RSAStar.Fake.perPort keyGen = Resource.ofProbAutomaton _
      (Lazy.step keyGen Lazy.signReduction (Lazy.verifyReduction fun _ _ _ => false))
      (Distribution.ProbDist.single none) :=
  (𝓡.freshSampling Salt M q (RSAStar.Fake.freshSampling keyGen _)).eq_fresh.trans
    (𝓡.ofProbAutomaton_eq Salt M (RSAStar.Fake.freshStep keyGen)
      (fun key _ => (some key, ((), ()))) (none, ((), ())) keyGen _ q
      (fun key _ => RSAStar.Fake.outcome_pk keyGen key)
      (fun key _ _ => RSAStar.Fake.outcome_challenge keyGen key)
      (fun key _ S => RSAStar.Fake.outcome_check keyGen key S)
      (fun _ _ _ _ _ => rfl) (RSAStar.Fake.outcome_none_pk keyGen)).symm

end Instances

end ReductionAutomaton

/-! ### Identical until bad -/

namespace Lazy

open Probability.Distribution

section UntilBad

variable {Salt : Type} [Fintype Salt] [Nonempty Salt] [DecidableEq Salt]
  {M : Type} [Fintype M] [DecidableEq M]

/-- **Bad**: a signature query has hit a point without a root. -/
def Bad : Option (State bits Salt M) → Prop
  | none => False
  | some s => s.bad = true

variable (keyGen : Distribution.ProbDist (RSA.Key bits))

/-- **The states reachable before bad** after the transcript `h`: a generated key, each point
programmed at `S^e` for its root `S`, the signatures issued exactly the programmed points with
their roots, and at most as many points without a root as oracle and verification queries. -/
def Reachable :
    List ((Σ i, SigRO.Input bits Salt M i) × (Σ i, SigRO.Output bits Salt i)) →
      Option (State bits Salt M) → Prop
  | _, none => True
  | h, some s => s.key ∈ keyGen.1.support ∧
      (∀ p Y S₀, s.H.lookup p = some (Y, some S₀) →
        S₀.val < s.key.N.val ∧ Y = s.key.pow S₀ s.key.e.val) ∧
      (∀ m R S, (m, R, S) ∈ s.signed ↔ ∃ Y, s.H.lookup (m, R) = some (Y, some S)) ∧
      (s.H.filter fun e => e.2.2.isNone).length ≤
        (SystemAlgebra.restrict SigningRO.Port.ro (h.map Prod.fst)).length +
          (SystemAlgebra.restrict SigningRO.Port.ver (h.map Prod.fst)).length

omit [Fintype M] [Fintype Salt] [Nonempty Salt] in
/-- A signature query of the reduction from a state that is not bad goes bad exactly at a point
without a root. -/
lemma signReduction_bad {s : State bits Salt M} (hs : s.bad = false) (m : M) (R : Salt)
    (S : RSA.Residue bits) :
    (signReduction s m R S).1.bad = true ↔ ∃ Y, s.H.lookup (m, R) = some (Y, none) := by
  unfold signReduction
  rcases hp : s.H.lookup (m, R) with _ | ⟨Y, _ | S₀⟩ <;> simp [hs]

/-- **The probability that a signature query goes bad**: from a state that is not bad, the
reduction goes bad at `sign(m)` with the probability that `m ‖ R` is a point without a root. -/
lemma mass_bad_sign (verify : State bits Salt M → M × Salt × RSA.Residue bits →
      RSA.Residue bits × Option (RSA.Residue bits) → Bool)
    {s : State bits Salt M} (hs : s.bad = false) (m : M) :
    (stepOn signReduction verify s .sign m).1.mass (fun p => p.1.bad = true) =
      (DSL.uniform Salt).1.mass fun R => ∃ Y, s.H.lookup (m, R) = some (Y, none) := by
  rw [stepOn_sign, mass_bindK]
  simp only [mass_fTransform, signReduction_bad hs]
  rw [mass, Finsupp.sum]
  refine Finset.sum_congr rfl fun R _ => ?_
  beta_reduce
  by_cases hR : ∃ Y, s.H.lookup (m, R) = some (Y, none)
  · rw [if_pos hR, show (RSA.residue s.key.N).1.mass (fun _ => ∃ Y,
      s.H.lookup (m, R) = some (Y, none)) = 1 by
        rw [mass_congr _ (Q := fun _ => True) fun _ => iff_true_intro hR, mass_true,
          (RSA.residue s.key.N).2.2], mul_one]
  · rw [if_neg hR, mass_eq_zero_of_forall_not _ fun _ => hR, mul_zero]

omit [Fintype M] in
/-- **Few points without a root**: the probability that `m ‖ R` is a point without a root, for a
uniform `R`, is at most their number over the number of salts. -/
lemma uniform_mass_lookup_le
    (table : List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits))) (m : M) :
    (DSL.uniform Salt).1.mass (fun R => ∃ Y, table.lookup (m, R) = some (Y, none)) ≤
      (table.filter fun e => e.2.2.isNone).length / Fintype.card Salt := by
  classical
  rw [show (DSL.uniform Salt).1 = Distribution.uniform Salt from rfl,
    uniform_mass_eq_card_filter]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  -- Each such `R` gives the point `m ‖ R` of an entry of the table without a root.
  have hsub : (Finset.univ.filter fun R => ∃ Y, table.lookup (m, R) = some (Y, none)).image
      (fun R => (m, R)) ⊆ ((table.filter fun e => e.2.2.isNone).map Prod.fst).toFinset := by
    intro p hp
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨Y, hY⟩ := (Finset.mem_filter.mp hR).2
    obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.mp hY
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨((m, R), Y, none), List.mem_filter.mpr ⟨by rw [hl]; simp, rfl⟩, rfl⟩
  calc ((Finset.univ.filter fun R => ∃ Y, table.lookup (m, R) = some (Y, none)).card : ℝ)
      = (((Finset.univ.filter fun R => ∃ Y, table.lookup (m, R) = some (Y, none)).image
          (fun R => (m, R))).card : ℝ) := by
        rw [Finset.card_image_of_injective _ fun R R' h => (Prod.mk.inj h).2]
    _ ≤ ((((table.filter fun e => e.2.2.isNone).map Prod.fst).toFinset).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (table.filter fun e => e.2.2.isNone).length := by
        exact_mod_cast (List.toFinset_card_le _).trans (List.length_map _).le

omit [DecidableEq M] [Nonempty Salt] [DecidableEq Salt] in
/-- The number of queries at a port, after the next query `x`. -/
lemma restrict_length_snoc (h : List ((Σ i, SigRO.Input bits Salt M i) ×
      (Σ i, SigRO.Output bits Salt i))) (x : Σ i, SigRO.Input bits Salt M i)
    (y : Σ i, SigRO.Output bits Salt i) (i : SigningRO.Port) :
    (SystemAlgebra.restrict i ((h ++ [(x, y)]).map Prod.fst)).length =
      (SystemAlgebra.restrict i (h.map Prod.fst)).length + if x.1 = i then 1 else 0 := by
  rw [List.map_append, List.map_singleton, SystemAlgebra.restrict_append, List.length_append,
    SystemAlgebra.length_restrict_singleton]
  congr 1
  by_cases hx : x.1 = i <;> simp [hx]

/-- **The reduction keeps its states reachable before bad**, after the first query. -/
lemma reachable_stepOn (chk : RSA.Key bits → List ((M × Salt) × RSA.Residue bits ×
      Option (RSA.Residue bits)) → RSA.Residue bits → Bool)
    {h : List ((Σ i, SigRO.Input bits Salt M i) × (Σ i, SigRO.Output bits Salt i))}
    {s : State bits Salt M} (hr : Reachable keyGen h (some s))
    (x : Σ i, SigRO.Input bits Salt M i)
    {t : State bits Salt M} {y : SigRO.Output bits Salt x.1}
    (hty : (t, y) ∈ (stepOn signReduction (verifyReduction chk) s x.1 x.2).1.support)
    (ht : t.bad = false) : Reachable keyGen (h ++ [(x, ⟨x.1, y⟩)]) (some t) := by
  obtain ⟨hkey, hprog, hsigned, hcount⟩ := hr
  simp only [Reachable]
  rw [restrict_length_snoc, restrict_length_snoc]
  obtain ⟨_ | _ | _ | _, x⟩ := x
  · rw [stepOn_pk, Finsupp.mem_support_single] at hty
    obtain ⟨⟨rfl, -⟩, -⟩ := hty
    exact ⟨hkey, hprog, hsigned, by simp; omega⟩
  · classical
    rw [stepOn_sign] at hty
    obtain ⟨R, -, hR⟩ := mem_support_bindK hty
    obtain ⟨S, hS, hSt⟩ := Finset.mem_image.mp (support_fTransform_subset _ _ hR)
    have hSN : S.val < s.key.N.val := RSA.lt_of_mem_support_residue s.key.2 hS
    unfold signReduction at hSt
    cases hp : s.H.lookup (x, R) with
    | none =>
      rw [hp] at hSt
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hSt
      refine ⟨hkey, fun p Y S₀ hp' => ?_, fun m' R' S' => ?_, ?_⟩
      · rw [List.lookup_append_of_lookup_eq_none hp] at hp'
        split_ifs at hp' with hpp
        · obtain ⟨rfl, rfl⟩ : s.key.pow S s.key.e.val = Y ∧ S = S₀ := by simpa using hp'
          exact ⟨hSN, rfl⟩
        · exact hprog p Y S₀ hp'
      · simp only [List.mem_append, List.mem_singleton, List.lookup_append_of_lookup_eq_none hp]
        by_cases hmR : (m', R') = (x, R)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmR
          rw [if_pos rfl, hsigned, hp]
          simp [eq_comm]
        · rw [if_neg hmR, hsigned]
          constructor
          · rintro (h₁ | h₁)
            · exact h₁
            · simp only [Prod.mk.injEq] at h₁
              exact absurd (by rw [h₁.1, h₁.2.1]) hmR
          · exact Or.inl
      · simp [List.filter_append]
        omega
    | some v =>
      obtain ⟨Y, _ | S₀⟩ := v
      · rw [hp] at hSt
        obtain ⟨rfl, -⟩ := Prod.mk.inj hSt
        exact absurd ht (by simp)
      · rw [hp] at hSt
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hSt
        refine ⟨hkey, hprog, fun m' R' S' => ?_, by simp; omega⟩
        simp only [List.mem_append, List.mem_singleton]
        rw [hsigned]
        constructor
        · rintro (h₁ | h₁)
          · exact h₁
          · obtain ⟨rfl, rfl, rfl⟩ : m' = x ∧ R' = R ∧ S' = S₀ := by simpa using h₁
            exact ⟨Y, hp⟩
        · exact Or.inl
  · obtain ⟨m, R, S⟩ := x
    cases hp : s.H.lookup (m, R) with
    | some v =>
      rw [stepOn_ver_some _ _ hp, Finsupp.mem_support_single] at hty
      obtain ⟨⟨rfl, -⟩, -⟩ := hty
      exact ⟨hkey, hprog, hsigned, by simp; omega⟩
    | none =>
      classical
      rw [stepOn_ver_none _ _ hp] at hty
      obtain ⟨Y, -, hYt⟩ := Finset.mem_image.mp (support_fTransform_subset _ _ hty)
      obtain ⟨rfl, -⟩ := Prod.mk.inj hYt
      refine ⟨hkey, fun p Y' S₀ hp' => ?_, fun m' R' S' => ?_, ?_⟩
      · simp only [State.define] at hp'
        rw [List.lookup_append_of_lookup_eq_none hp] at hp'
        split_ifs at hp' with hpp
        · simp at hp'
        · exact hprog p Y' S₀ hp'
      · simp only [State.define, List.lookup_append_of_lookup_eq_none hp]
        rw [hsigned]
        by_cases hmR : (m', R') = (m, R)
        · rw [if_pos hmR]
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmR
          rw [hp]
          simp
        · rw [if_neg hmR]
      · simp [State.define, List.filter_append]
        omega
  · obtain ⟨m, R⟩ := x
    cases hp : s.H.lookup (m, R) with
    | some v =>
      rw [stepOn_ro_some _ _ hp, Finsupp.mem_support_single] at hty
      obtain ⟨⟨rfl, -⟩, -⟩ := hty
      exact ⟨hkey, hprog, hsigned, by simp; omega⟩
    | none =>
      classical
      rw [stepOn_ro_none _ _ hp] at hty
      obtain ⟨Y, -, hYt⟩ := Finset.mem_image.mp (support_fTransform_subset _ _ hty)
      obtain ⟨rfl, -⟩ := Prod.mk.inj hYt
      refine ⟨hkey, fun p Y' S₀ hp' => ?_, fun m' R' S' => ?_, ?_⟩
      · simp only [State.define] at hp'
        rw [List.lookup_append_of_lookup_eq_none hp] at hp'
        split_ifs at hp' with hpp
        · simp at hp'
        · exact hprog p Y' S₀ hp'
      · simp only [State.define, List.lookup_append_of_lookup_eq_none hp]
        rw [hsigned]
        by_cases hmR : (m', R') = (m, R)
        · rw [if_pos hmR]
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmR
          rw [hp]
          simp
        · rw [if_neg hmR]
      · simp [State.define, List.filter_append]
        omega

omit [Fintype M] [DecidableEq M] [Fintype Salt] [Nonempty Salt] [DecidableEq Salt] in
/-- A law with no mass on an event has nothing left once restricted to it. -/
lemma restrict_fTransform_eq_zero {A : Type}
    {f : A → State bits Salt M × (Salt × RSA.Residue bits)}
    (μ : Distribution A) (hf : ∀ a, (f a).1.bad = true) :
    (fTransform f μ).restrict (fun p => ¬ p.1.bad = true) = 0 := by
  rw [restrict_fTransform, restrict_congr μ (Q := fun _ => False) fun a => by simp [hf a],
    restrict_false]
  simp [fTransform]

/-- **Signing is the same until bad**: from a reachable state that is not bad, the reduction and
the libraries sign alike, the next states not bad: at a new point, `S ↦ S^e` is a permutation
of `ℤ_N` undone by `d`; at a programmed point, `Y^d` is its root. -/
lemma restrict_stepOn_sign (correct : RSA.Correct keyGen)
    {h : List ((Σ i, SigRO.Input bits Salt M i) × (Σ i, SigRO.Output bits Salt i))}
    {s : State bits Salt M} (hr : Reachable keyGen h (some s))
    (v₁ v₂ : State bits Salt M → M × Salt × RSA.Residue bits →
      RSA.Residue bits × Option (RSA.Residue bits) → Bool) (m : M) :
    (stepOn signReduction v₁ s .sign m).1.restrict (fun p => ¬ p.1.bad = true) =
      (stepOn signLibrary v₂ s .sign m).1.restrict (fun p => ¬ p.1.bad = true) := by
  obtain ⟨hkey, hprog, -, -⟩ := hr
  have hc := correct s.key hkey
  rw [stepOn_sign, stepOn_sign, restrict_bindK, restrict_bindK]
  refine bindK_congr fun R _ => ?_
  cases hp : s.H.lookup (m, R) with
  | none =>
    have e : fTransform (signReduction s m R) (RSA.residue s.key.N).1 =
        fTransform (signLibrary s m R) (RSA.residue s.key.N).1 := by
      conv_rhs => rw [← RSA.residue_pow s.key hc]
      rw [fTransform_fTransform]
      refine fTransform_congr_support fun S hS => ?_
      have hSN := RSA.lt_of_mem_support_residue s.key.2 hS
      simp [signReduction, signLibrary, hp, hc S hSN]
    rw [e]
  | some v =>
    obtain ⟨Y, _ | S₀⟩ := v
    · rw [restrict_fTransform_eq_zero _ fun S => by simp [signReduction, hp],
        restrict_fTransform_eq_zero _ fun S => by simp [signLibrary, hp]]
    · obtain ⟨hS₀, rfl⟩ := hprog _ _ _ hp
      have e : signReduction s m R = signLibrary s m R := funext fun S => by
        simp [signReduction, signLibrary, hp, hc S₀ hS₀]
      rw [e]

omit [Fintype M] [Fintype Salt] [Nonempty Salt] in
/-- The value of a point without a root is a challenge. -/
lemma mem_challenges_of_lookup
    {table : List ((M × Salt) × RSA.Residue bits × Option (RSA.Residue bits))}
    {p : M × Salt} {Y : RSA.Residue bits} (hp : table.lookup p = some (Y, none)) :
    Y ∈ challenges table := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp hp
  simp [challenges, List.filterMap_append]

/-- **Verification against `rsa*-real` is the verification equation**: `check*(S)` at a point
without a root of value `Y = S^e` finds `Y` among the challenges. -/
lemma stepOn_ver_real (s : State bits Salt M) (x : M × Salt × RSA.Residue bits) :
    (stepOn signReduction (verifyReduction fun key table S =>
        decide (key.pow S key.e.val ∈ challenges table)) s .ver x).1 =
      (stepOn signLibrary verifyReal s .ver x).1 := by
  obtain ⟨m, R, S⟩ := x
  have hv : ∀ (t : State bits Salt M) (Y : RSA.Residue bits)
      (r : Option (RSA.Residue bits)), (r = none → Y ∈ challenges t.H) →
      verifyReduction (fun key table S => decide (key.pow S key.e.val ∈ challenges table)) t
        (m, R, S) (Y, r) = verifyReal t (m, R, S) (Y, r) := by
    intro t Y r hY
    cases r with
    | some _ => rfl
    | none =>
      simp only [verifyReduction, verifyReal]
      split_ifs with hg
      · obtain ⟨hS, he⟩ := hg
        rw [← he]
        simp [hY rfl, hS]
      · exact (decide_eq_false hg).symm
  cases hp : s.H.lookup (m, R) with
  | some v =>
    rw [stepOn_ver_some _ _ hp, stepOn_ver_some _ _ hp, hv s v.1 v.2 fun hr =>
      mem_challenges_of_lookup (show s.H.lookup (m, R) = some (v.1, none) by rw [hp, ← hr])]
  | none =>
    rw [stepOn_ver_none _ _ hp, stepOn_ver_none _ _ hp]
    congr 1
    funext Y
    rw [hv _ Y none fun _ => by simp [State.define, challenges_append_none]]

/-- **Verification against `rsa*-fake` is membership in `𝒮`**, from a reachable state: at a
programmed point the verification equation holds exactly at its root, the signature issued. -/
lemma stepOn_ver_fake (correct : RSA.Correct keyGen)
    {h : List ((Σ i, SigRO.Input bits Salt M i) × (Σ i, SigRO.Output bits Salt i))}
    {s : State bits Salt M} (hr : Reachable keyGen h (some s))
    (x : M × Salt × RSA.Residue bits) :
    (stepOn signReduction (verifyReduction fun _ _ _ => false) s .ver x).1 =
      (stepOn signLibrary verifyFake s .ver x).1 := by
  obtain ⟨hkey, hprog, hsigned, -⟩ := hr
  obtain ⟨m, R, S⟩ := x
  have hc := correct s.key hkey
  cases hp : s.H.lookup (m, R) with
  | some v =>
    rw [stepOn_ver_some _ _ hp, stepOn_ver_some _ _ hp]
    congr 3
    obtain ⟨Y, _ | S₀⟩ := v
    · simp only [verifyReduction, verifyFake, ite_self]
      refine (decide_eq_false fun hm => ?_).symm
      obtain ⟨Y', hY'⟩ := (hsigned m R S).mp hm
      rw [hp] at hY'
      simp at hY'
    · obtain ⟨hS₀, rfl⟩ := hprog _ _ _ hp
      simp only [verifyReduction, verifyFake]
      refine decide_eq_decide.mpr ⟨fun ⟨hS, he⟩ => (hsigned m R S).mpr ?_, fun hm => ?_⟩
      · exact ⟨s.key.pow S₀ s.key.e.val, by rw [hp, show S₀ = S by rw [← hc S₀ hS₀, he, hc S hS]]⟩
      · obtain ⟨Y', hY'⟩ := (hsigned m R S).mp hm
        rw [hp] at hY'
        obtain ⟨-, rfl⟩ : s.key.pow S₀ s.key.e.val = Y' ∧ S₀ = S := by simpa using hY'
        exact ⟨hS₀, rfl⟩
  | none =>
    rw [stepOn_ver_none _ _ hp, stepOn_ver_none _ _ hp]
    congr 1
    funext Y
    refine Prod.ext rfl ?_
    dsimp only [verifyReduction, verifyFake, State.define]
    rw [ite_self]
    refine (decide_eq_false fun hm => ?_).symm
    obtain ⟨Y', hY'⟩ := (hsigned m R S).mp hm
    rw [hp] at hY'
    simp at hY'

omit [Nonempty Salt] in
/-- The state of a generated key with nothing defined is reachable. -/
lemma reachable_initial {key : RSA.Key bits} (hkey : key ∈ keyGen.1.support)
    (h : List ((Σ i, SigRO.Input bits Salt M i) × (Σ i, SigRO.Output bits Salt i))) :
    Reachable keyGen h (some ⟨key, [], [], false⟩) :=
  ⟨hkey, fun _ _ _ hp => by simp at hp, fun _ _ _ => by simp, by simp⟩

/-- **The reduction and a library are identical until bad**: if they verify alike from the
reachable states that are not bad, the automata of the reduction and of the library, at most
`q i` queries at each port `i`, are within `q_sign · (q_ro + q_ver) / |Salt|`. -/
lemma distance_le (correct : RSA.Correct keyGen) (q : SigningRO.Port → ℕ)
    (chk : RSA.Key bits → List ((M × Salt) × RSA.Residue bits ×
      Option (RSA.Residue bits)) → RSA.Residue bits → Bool)
    (verify : State bits Salt M → M × Salt × RSA.Residue bits →
      RSA.Residue bits × Option (RSA.Residue bits) → Bool)
    (hver : ∀ h s, Reachable keyGen h (some s) → ∀ x,
      (stepOn signReduction (verifyReduction chk) s .ver x).1 =
        (stepOn signLibrary verify s .ver x).1) :
    Δ (Resource.ofProbAutomaton (SigRO.perPort bits Salt M q)
        (step keyGen signReduction (verifyReduction chk)) (Distribution.ProbDist.single none))
      (Resource.ofProbAutomaton (SigRO.perPort bits Salt M q)
        (step keyGen signLibrary verify) (Distribution.ProbDist.single none)) ≤
      ENNReal.ofReal ((q .sign : ℝ) * (q .ro + q .ver) / Fintype.card Salt) := by
  classical
  -- The steps from the states after the first query.
  have hpres : ∀ h s x, Reachable keyGen h (some s) → s.bad = false →
      ∀ p ∈ ((step keyGen signReduction (verifyReduction chk)).outcome (some s) x).support,
        ¬ Bad p.1 → Reachable keyGen (h ++ [(x, p.2)]) p.1 := by
    intro h s x hr hs p hp hb
    rw [step_outcome_some] at hp
    obtain ⟨⟨t, y⟩, hty, rfl⟩ := Finset.mem_image.mp (support_fTransform_subset _ _ hp)
    exact reachable_stepOn keyGen chk hr x hty (by simpa [Bad] using hb)
  have hstep : ∀ h s x, Reachable keyGen h (some s) → s.bad = false →
      ((step keyGen signReduction (verifyReduction chk)).outcome (some s) x).restrict
          (fun p => ¬ Bad p.1) =
        ((step keyGen signLibrary verify).outcome (some s) x).restrict fun p => ¬ Bad p.1 := by
    intro h s x hr hs
    rw [step_outcome_some, step_outcome_some, restrict_fTransform, restrict_fTransform]
    refine congrArg _ ?_
    obtain ⟨_ | _ | _ | _, x⟩ := x
    · rfl
    · exact restrict_stepOn_sign keyGen correct hr _ _ x
    · rw [hver h s hr x]
    · rfl
  -- The probability of going bad at a query.
  set β : SigningRO.Port → ℝ := fun
    | .sign => ((q .ro + q .ver : ℕ) : ℝ) / Fintype.card Salt
    | _ => 0 with hβdef
  have hβ : ∀ h s x, Reachable keyGen h (some s) → s.bad = false →
      (SigRO.perPort bits Salt M q).domain (h.map Prod.fst ++ [x]) →
      ((step keyGen signReduction (verifyReduction chk)).outcome (some s) x).mass
        (fun p => Bad p.1) ≤ β x.1 := by
    intro h s x hr hs hd
    rw [step_outcome_some, mass_fTransform]
    change (stepOn signReduction (verifyReduction chk) s x.1 x.2).1.mass
      (fun p => p.1.bad = true) ≤ β x.1
    obtain ⟨_ | _ | _ | _, x⟩ := x
    · rw [stepOn_pk, mass_single]
      simp [hs, hβdef]
    · rw [mass_bad_sign _ hs]
      refine (uniform_mass_lookup_le s.H x).trans ?_
      have hro := hd.2 .ro
      have hver := hd.2 .ver
      simp only [SystemAlgebra.restrict_append, List.length_append] at hro hver
      have hc := hr.2.2.2
      simp only [hβdef]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact_mod_cast hc.trans (by omega)
    · obtain ⟨m, R, S⟩ := x
      cases hp : s.H.lookup (m, R) with
      | some v =>
        rw [stepOn_ver_some _ _ hp, mass_single]
        simp [hs, hβdef]
      | none =>
        rw [stepOn_ver_none _ _ hp, mass_fTransform,
          mass_eq_zero_of_forall_not _ fun Y => by simp [State.define, hs]]
    · obtain ⟨m, R⟩ := x
      cases hp : s.H.lookup (m, R) with
      | some v =>
        rw [stepOn_ro_some _ _ hp, mass_single]
        simp [hs, hβdef]
      | none =>
        rw [stepOn_ro_none _ _ hp, mass_fTransform,
          mass_eq_zero_of_forall_not _ fun Y => by simp [State.define, hs]]
  refine (Interface.Resource.distance_ofProbAutomaton_le (T := SigRO.perPort bits Salt M q)
    _ _ _ Bad (Reachable keyGen) (fun s hs => ?_) (fun h s x hr hb hd p hp hpb => ?_)
    (fun h s x hr hb hd => ?_) q (fun _ hd => hd.2) β (fun i => by cases i <;> positivity)
    (fun h s x hr hb hd => ?_)).trans (le_of_eq ?_)
  · rw [show s = none from (Finsupp.mem_support_single _ _ _).mp hs |>.1]
    exact ⟨trivial, id⟩
  · cases s with
    | none =>
      rw [step_outcome_none] at hp
      obtain ⟨key, hkey, hp⟩ := mem_support_bindK hp
      exact hpres h _ x (reachable_initial keyGen hkey h) rfl p hp hpb
    | some s => exact hpres h s x hr (by simpa [Bad] using hb) p hp hpb
  · cases s with
    | none =>
      rw [step_outcome_none, step_outcome_none, restrict_bindK, restrict_bindK]
      exact bindK_congr fun key hkey => hstep h _ x (reachable_initial keyGen hkey h) rfl
    | some s => exact hstep h s x hr (by simpa [Bad] using hb)
  · cases s with
    | none =>
      rw [step_outcome_none, mass_bindK]
      calc keyGen.1.sum (fun key w => w * ((step keyGen signReduction
              (verifyReduction chk)).outcome (some ⟨key, [], [], false⟩) x).mass fun p => Bad p.1)
          ≤ keyGen.1.sum fun _ w => w * β x.1 := Finset.sum_le_sum fun key hkey =>
            mul_le_mul_of_nonneg_left (hβ h _ x (reachable_initial keyGen hkey h) rfl hd)
              (keyGen.2.1 key)
        _ = β x.1 := by
          rw [Finsupp.sum, ← Finset.sum_mul, show (∑ key ∈ keyGen.1.support, keyGen.1 key) = 1
            from keyGen.2.2, one_mul]
    | some s => exact hβ h s x hr (by simpa [Bad] using hb) hd
  · congr 1
    simp [hβdef, Finset.univ, Fintype.elems]
    ring

end UntilBad

end Lazy

section Distance

variable (Salt : Type) [Fintype Salt] [Nonempty Salt] [DecidableEq Salt]
  (M : Type) [Fintype M] [DecidableEq M]
  (keyGen : Distribution.ProbDist (RSA.Key bits))

/-- **`sig-real+ro` is `𝓡` on `rsa*-real` until bad**: they differ only once a signature query
hits a point of the oracle defined by an oracle or a verification query, which happens with
probability at most `q_sign · (q_ro + q_ver) / |Salt|`. -/
lemma 𝓡.distance_real (correct : RSA.Correct keyGen) (q : SigningRO.Port → ℕ) :
    Δ (SigReal Salt M keyGen q)
      (𝓡.perLabel Salt M q • RSAStar.Real.perPort keyGen) ≤
        ENNReal.ofReal ((q .sign : ℝ) * (q .ro + q .ver) / Fintype.card Salt) := by
  rw [SigReal.eq_lazy, 𝓡.smul_real,
    ConstructiveCryptography.CryptographicAlgebra.distance_comm]
  exact Lazy.distance_le keyGen correct q _ Lazy.verifyReal fun _ s _ x =>
    Lazy.stepOn_ver_real s x

/-- **`𝓡` on `rsa*-fake` is `sig-fake` until bad**: they differ only once a signature query
hits a point of the oracle defined by an oracle or a verification query, which happens with
probability at most `q_sign · (q_ro + q_ver) / |Salt|`. -/
lemma 𝓡.distance_fake (correct : RSA.Correct keyGen) (q : SigningRO.Port → ℕ) :
    Δ (𝓡.perLabel Salt M q • RSAStar.Fake.perPort keyGen :
        Resource (SigRO.perPort bits Salt M q))
      (SigFake.perPort Salt M keyGen (budget := q)) ≤
        ENNReal.ofReal ((q .sign : ℝ) * (q .ro + q .ver) / Fintype.card Salt) := by
  rw [SigFake.perPort_eq_lazy, 𝓡.smul_fake]
  exact Lazy.distance_le keyGen correct q _ Lazy.verifyFake fun _ _ hr x =>
    Lazy.stepOn_ver_fake keyGen correct hr x

end Distance

/-! ## RSA-PSS -/

/-- **RSA-PSS from the many-challenge assumption**: if `rsa*-real` substitutes for `rsa*-fake`
within `ε`, then `sig-real+ro` substitutes for `sig-fake` within `ε` at the distinguisher with `𝓡`
absorbed and twice the probability that a signature query hits a point of the oracle defined by
an oracle or a verification query. -/
theorem rsa_pss_of_rsaStar [AdmissibleDistinguishers]
    (Salt : Type) [Fintype Salt] [Nonempty Salt] [DecidableEq Salt] (M : Type) [Fintype M]
    [DecidableEq M] (keyGen : Distribution.ProbDist (RSA.Key bits)) (correct : RSA.Correct keyGen)
    (q : SigningRO.Port → ℕ) :
    ∀ ε, RSAStar.Assumption keyGen ε →
      SigReal Salt M keyGen q ≃[fun D => ε (absorb (𝓡.perLabel Salt M q) D) +
          ENNReal.ofReal (2 * (q .sign : ℝ) * (q .ro + q .ver) / Fintype.card Salt)]
        SignatureScheme.FakeRO.perPort _ _ _ _ _ • SigReal Salt M keyGen q := by
  intro ε secure
  have chain : SigReal Salt M keyGen q ≃[fun D =>
      ENNReal.ofReal ((q .sign : ℝ) * (q .ro + q .ver) / Fintype.card Salt) +
        ε (absorb (𝓡.perLabel Salt M q) D) +
        ENNReal.ofReal ((q .sign : ℝ) * (q .ro + q .ver) / Fintype.card Salt)]
      SignatureScheme.FakeRO.perPort _ _ _ _ _ • SigReal Salt M keyGen q := by
    cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
        (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
      SigReal Salt M keyGen q ≈[ENNReal.ofReal ((q .sign : ℝ) * (q .ro + q .ver) /
          Fintype.card Salt)] 𝓡.perLabel Salt M q • RSAStar.Real.perPort keyGen :=
        𝓡.distance_real Salt M keyGen correct q
      _ ≃[ε ∘ absorb (𝓡.perLabel Salt M q)] (𝓡.perLabel Salt M q •
          (RSAStar.Reject.perPort bits • RSAStar.Real.perPort keyGen) :
            Resource (SigRO.perPort bits Salt M q)) :=
        AdmissibleDistinguishers.substitutesWithin_context _ secure
      _ = (𝓡.perLabel Salt M q • RSAStar.Fake.perPort keyGen :
            Resource (SigRO.perPort bits Salt M q)) := by
        rw [RSAStar.Fake.perPort_eq_reject]
      _ ≈[ENNReal.ofReal ((q .sign : ℝ) * (q .ro + q .ver) / Fintype.card Salt)]
          SigFake.perPort Salt M keyGen := 𝓡.distance_fake Salt M keyGen correct q
      _ = SignatureScheme.FakeRO.perPort _ _ _ _ _ • SigReal Salt M keyGen q :=
        SigFake.perPort_eq_fakeRO Salt M keyGen q
  -- The two programming losses together.
  refine ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.mono
    _ chain fun D _ => le_of_eq ?_
  have hx : (0 : ℝ) ≤ (q .sign : ℝ) * (q .ro + q .ver) / Fintype.card Salt := by positivity
  rw [show 2 * (q .sign : ℝ) * (q .ro + q .ver) / Fintype.card Salt =
      (q .sign : ℝ) * (q .ro + q .ver) / Fintype.card Salt +
        (q .sign : ℝ) * (q .ro + q .ver) / Fintype.card Salt
    by ring, ENNReal.ofReal_add hx hx]
  ring

/-- **The loss of the two reductions composed**: the many-challenge loss at the distinguisher with
`𝓡₁` absorbed, after the self-reduction `𝓡₂`, is the RSA loss at `𝓡₁ ≫ 𝓡₂` absorbed and the
non-unit loss of the `q_ver + q_ro` challenges and of the challenge of the assumption. -/
lemma composed_loss_eq {A B C : Interface} (𝓡₁ : A ⟶ B) (𝓡₂ : B ⟶ C)
    (ε : C.inputDomain.DistinguisherBehavior → ENNReal) (D : A.inputDomain.DistinguisherBehavior)
    (qver qro : ℕ) (δ loss : ℝ) :
    ε (absorb 𝓡₂ (absorb 𝓡₁ D)) + ENNReal.ofReal ((((qver + qro : ℕ) : ℝ) + 1) * δ) +
        ENNReal.ofReal loss =
      ε (absorb (𝓡₁ ≫ 𝓡₂) D) + ENNReal.ofReal (((qver : ℝ) + qro + 1) * δ) +
        ENNReal.ofReal loss := by
  rw [absorb_comp]
  push_cast
  rfl

/-- **RSA-PSS** [1, §8.2]: if the RSA assumption holds within `ε`, then `sig-real+ro`
substitutes for `sig-fake` within `ε` at the distinguisher with `𝓡` and the self-reduction
absorbed, the non-unit losses of the self-reduction, and the programming loss. -/
theorem rsa_pss [AdmissibleDistinguishers]
    (Salt : Type) [Fintype Salt] [Nonempty Salt] [DecidableEq Salt]
    (M : Type) [Fintype M] [DecidableEq M]
    (keyGen : Distribution.ProbDist (RSA.Key bits)) (correct : RSA.Correct keyGen) (δ : ℝ)
    (nonUnit : RSA.NonUnitBound keyGen δ) (q : SigningRO.Port → ℕ) :
    ∀ ε, RSA.Assumption keyGen ε →
      SigReal Salt M keyGen q ≃[fun D =>
          ε (absorb (𝓡.perLabel Salt M q ≫ RSAStar.selfReduction (insideBudget q)) D) +
            ENNReal.ofReal (((q .ver : ℝ) + q .ro + 1) * δ) +
            ENNReal.ofReal (2 * (q .sign : ℝ) * (q .ro + q .ver) / Fintype.card Salt)]
        SignatureScheme.FakeRO.perPort _ _ _ _ _ • SigReal Salt M keyGen q := by
  intro ε secure
  exact ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.mono
    _ (rsa_pss_of_rsaStar Salt M keyGen correct q _
      (rsa_self_reduction keyGen correct δ nonUnit (insideBudget q) ε secure)) fun D _ =>
    le_of_eq (composed_loss_eq (𝓡.perLabel Salt M q) (RSAStar.selfReduction (insideBudget q))
      ε D _ _ δ _)


/-- **RSA-PSS with `λ`-bit salts** [1, §8.2]: `rsa_pss` at the notes' salts `R ∈ {0,1}^λ`, with
the programming loss `2 q_sign (q_ro + q_ver) / 2^λ`. -/
theorem rsa_pss_bits [AdmissibleDistinguishers] (secpar : ℕ) (M : Type) [Fintype M]
    [DecidableEq M] (keyGen : Distribution.ProbDist (RSA.Key bits)) (correct : RSA.Correct keyGen)
    (δ : ℝ) (nonUnit : RSA.NonUnitBound keyGen δ) (q : SigningRO.Port → ℕ) :
    ∀ ε, RSA.Assumption keyGen ε →
      SigReal (Bits secpar) M keyGen q ≃[fun D =>
          ε (absorb (𝓡.perLabel (Bits secpar) M q ≫ RSAStar.selfReduction (insideBudget q)) D) +
            ENNReal.ofReal (((q .ver : ℝ) + q .ro + 1) * δ) +
            ENNReal.ofReal (2 * (q .sign : ℝ) * (q .ro + q .ver) / 2 ^ secpar)]
        SignatureScheme.FakeRO.perPort _ _ _ _ _ • SigReal (Bits secpar) M keyGen q := by
  intro ε secure
  simpa only [card_bits, Nat.cast_pow, Nat.cast_ofNat] using
    rsa_pss (Bits secpar) M keyGen correct δ nonUnit q ε secure

end

end ProofLadders.RSAPSS
