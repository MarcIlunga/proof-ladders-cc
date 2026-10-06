import Commons.Definitions.Ideal
import Commons.Definitions.KEM
import ProofLadders.Common.Programs
import ProofLadders.Common.RSA
import ProofLadders.Common.Symmetric

/-!
# RSA-KEM

The RSA-KEM problem of the ladder [1, §7]: if the RSA assumption holds, then RSA-KEM,

$$\mathsf{Encaps}(N, e):\ R \leftarrow \mathbb{Z}_N,\ c := R^e \bmod N,\ K := \mathsf{RO}(R);
\qquad \mathsf{Decaps}((N, d), c) = \mathsf{RO}(c^d \bmod N),$$

is IND$-CCA-secure in the random-oracle model, for a single challenge.

A KEM in the random-oracle model is a KEM whose algorithms take the oracle `RO : A → H`. Its real
system samples a uniform oracle once and puts it beside the real system of the KEM with that
oracle. Single-challenge IND$-CCA security is a pair of converters on the real system, for every
such KEM: `kem-1cca-real+ro` takes one real encapsulation as the challenge `(c*, K*)`, and
`kem-1cca-rand+ro` answers with a random ciphertext `c*` under the public key and a uniform key
`K*`, and decapsulates `c*` to `K*`; both forward decapsulation and the oracle. The two converters
on the real system of a KEM are sampled functions of the oracle, the keys and the challenge.

RSA-KEM is such a KEM with the keys `K` a finite type, of which the notes' `{0,1}^λ` is an
instance, and the oracle `RO : RSA.Residue bits → K`. The modulus `N` is sampled while interface
alphabets are fixed, so the residues of every modulus share the type `RSA.Residue bits`, which
holds `ℤ_N` as the representatives `0, …, N − 1` of `ZMod N`. Ciphertexts range over it,
decapsulation answers `⊥` to those that are not residues modulo `N`, and the random ciphertext
under `(N, e)` is uniform in `ℤ_N`. The notes' libraries `kem-1cca-real+ro` and
`kem-1cca-rand+ro` are the two converters on the real system of RSA-KEM.

The reduction never needs `d`: it takes `(N, e, Y)` from `rsa.challenge()`, answers `c* := Y`
with a uniform `K*`, decapsulates `c ≠ c*` from a uniform table `T` indexed by `c`, and answers an
oracle query `A < N` with `K*` when `rsa.check(A)` and from the table at `A^e mod N` otherwise,
and `A ≥ N` from the table at `A`; it samples `T` and `K*` once. On `rsa-real` this is the real
library, at `R* := Y^d` and the oracle `T[Y ↦ K*] ∘ σ` for `σ` raising to `e` on `ℤ_N`, a
permutation by correctness; on `rsa-fake` it is the random one, at the oracle `T ∘ σ`. The
reduction calls `rsa.challenge()` on every query and `rsa.check` on oracle queries, so it is typed
at per-label inside budgets.

Style: pure random systems; both steps are equalities, and the loss is the RSA loss at the reduced
distinguisher.

Upstream candidates, for `Common/PublicKey`: `KEMOneCCA`, `KEM.RealRO`, `KEM.OneCCAReal`,
`KEM.OneCCARand`, their typing, their steps against a KEM (`KEM.OneCCAReal.combine_pk`, …), their
answers, `KEM.OneCCA.systems`, `KEM.OneCCA`, `KEM.OneCCAReal.smul_realRO` and
`KEM.OneCCARand.smul_realRO`, with the steps of the real system of a KEM against its sources
(`KEM.Real.combine_publicKey_none`, …); for `Common/Probability`,
`Distribution.fTransform_prod_fiber_congr`; for `Common/Functional`,
`SystemAlgebra.restrict_ne_nil_of_mem`, `Interface.Resource.ofFunction_congr_portBudget`,
`Interface.Resource.sample_const` and `Interface.Resource.ofAutomaton_eq_sample_of_law`.

## Main definitions

* `KEMOneCCA PK C K A H`: the interface of the single-challenge libraries with the oracle
* `KEM.RealRO kem`: the real system of a KEM in the random-oracle model
* `KEM.OneCCAReal`, `KEM.OneCCARand ciphertexts`, and their typing `perLabel`:
  `kem-1cca-real+ro` and `kem-1cca-rand+ro` as converters on it
* `KEM.OneCCA.systems kem ciphertexts q`, `KEM.OneCCA kem ciphertexts error`: single-challenge
  IND$-CCA security in the random-oracle model
* `scheme K keyGen`: RSA-KEM, with its oracle; `ciphertexts`: the uniform law on `ℤ_N`
* `OneCCA bits K q`: the interface of the RSA-KEM libraries
* `encapsulate`, `decapsulate`: RSA-KEM on the randomness `R`, the key and the oracle
* `Real keyGen`, `Rand keyGen`: the notes' `kem-1cca-real+ro` and `kem-1cca-rand+ro`
* `Real.sampled`, `Rand.sampled`: the two libraries as sampled functions
* `𝓡 bits K`, `𝓡.perLabel q`: the reduction, and its typing at per-label inside budgets
* `reductionAnswers`: the reduction's answers on an RSA library
* `realIndex`, `fakeIndex`: the samples of the two libraries from those of the reduction

## Main results

* `KEM.OneCCAReal.smul_realRO`, `KEM.OneCCARand.smul_realRO`: the two converters on the real
  system of a KEM are sampled functions
* `Real.perPort_eq_oneCCAReal`, `Rand.perPort_eq_oneCCARand`: the notes' libraries are the two
  converters on the real system of RSA-KEM
* `rsa_kem_cca`: RSA-KEM is single-challenge IND$-CCA-secure
* `𝓡_smul_real`, `𝓡_smul_fake`: the reduction on `rsa-real` is `kem-1cca-real+ro`, on
  `rsa-fake` it is `kem-1cca-rand+ro`
* `𝓡.labelBounded`, `𝓡.smul_ofFunction`, `𝓡.smul_sample`: the reduction's per-label call
  bound, and the reduction on an RSA library and on a sampled one
* `realIndex_law`, `reduction_real_sampled`, `fakeIndex_law`, `reduction_fake_sampled`: the
  re-indexed samples have the libraries' laws, and the reduction answers as the libraries
* `Real.perPort_eq_sampled`, `Rand.perPort_eq_sampled`, `Rand.sampled_eq_power`: the libraries
  as sampled functions, and `c* = R*^e`
* `rsa_kem_cca_sampled`: the theorem on sampled functions

## References

1. The symmetric proof ladder, *Security proofs in the style of The Joy of Cryptography*,
   `proof-ladders/symmetric-ladder`, `Notes/selfcontained.tex`.
-/

/-! ## Upstream candidate (Common/PublicKey)

A KEM in the random-oracle model, its real system, and single-challenge IND$-CCA security as a
pair of converters on it. -/

namespace Commons

open SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface Probability CategoryTheory
open scoped SystemAlgebra SystemAlgebra.DSL

interface KEMOneCCA(PK C K A H : Type) [Fintype PK] [Fintype C] [Fintype K] [Fintype A] [Fintype H]
  pk() → PK
  enc() → C × K
  dec(c : C) → Option K
  ro(a : A) → H

-- `kem-1cca-real+ro` [1, §7]: forward `pk()`; the first `enc()` takes `(c*, K*) ← kem.encaps()`,
-- and every `enc()` returns `(c*, K*)`; forward `dec(c)` and `ro(a)`.
converter KEM.OneCCAReal(PK C K A H : Type) [Fintype PK] [Fintype C] [Fintype K] [Fintype A] [Fintype H] : KEMOneCCA PK C K A H
  inside kem : Encapsulation PK C K
  inside oracle : Evaluation A H
  initialize
    challenge ← (none : Option (C × K))
  on pk() → PK
    pk ← kem.publicKey()
    return pk
  on enc() → C × K
    match challenge
    | some ck →
      return ck
    | none →
      ck ← kem.encaps()
      challenge ← some ck
      return ck
  on dec(c : C) → Option K
    k ← kem.decaps(c)
    return k
  on ro(a : A) → H
    h ← oracle.eval(a)
    return h

-- `kem-1cca-rand+ro` [1, §7]: `c* ← ciphertexts(pk)` for every public key `pk`, and `K* ← K`;
-- forward `pk()`; `enc()` returns `(c*, K*)` for `pk ← kem.publicKey()`; `dec(c*)` returns
-- `K*`, and `dec(c)` is forwarded otherwise; forward `ro(a)`.
converter KEM.OneCCARand(PK C K A H : Type) [Fintype PK] [Fintype C] [Fintype K] [Fintype A] [Fintype H] [DecidableEq PK] [DecidableEq C] [Nonempty K] (ciphertexts : PK → Distribution.ProbDist C) : KEMOneCCA PK C K A H
  inside kem : Encapsulation PK C K
  inside oracle : Evaluation A H
  initialize
    cstars ←$ Distribution.ProbDist.pi ciphertexts
    kstar ←$ 𝒰[K]
  on pk() → PK
    pk ← kem.publicKey()
    return pk
  on enc() → C × K
    pk ← kem.publicKey()
    return (cstars pk, kstar)
  on dec(c : C) → Option K
    pk ← kem.publicKey()
    if c = cstars pk
      return some kstar
    else
      k ← kem.decaps(c)
      return k
  on ro(a : A) → H
    h ← oracle.eval(a)
    return h

noncomputable section

variable {PK SK C K A H : Type} [Fintype PK] [Fintype SK] [Fintype C] [Fintype K] [Fintype A]
  [Fintype H]

/-- **The real system of a KEM in the random-oracle model**: a uniform oracle `RO : A → H`
sampled once, the real system of the KEM with `RO`, and `RO` beside it. -/
def KEM.RealRO [DecidableEq PK] [DecidableEq A] [Nonempty H] (kem : (A → H) → KEM PK SK C K)
    (q : Encapsulation.Port → ℕ) (n : ℕ) :
    Resource ((Encapsulation.perPort PK C K q).tensor (Evaluation A H n)) :=
  Resource.sample (Distribution.uniform (A → H)) fun RO =>
    KEM.Real.perPort (kem RO) ∥ Resource.ofFunction fun _ => RO

/-- The inside budget of the single-challenge converters: `kem.publicKey()` once per query,
`kem.encaps()` once per challenge query, and `kem.decaps` once per decapsulation query. -/
abbrev KEM.OneCCA.insideBudget (q : KEMOneCCA.Port → ℕ) : Encapsulation.Port → ℕ
  | .publicKey => q .pk + q .enc + q .dec
  | .encaps => q .enc
  | .decaps => q .dec

/-- The inside interface of the single-challenge converters: the KEM beside the oracle. -/
abbrev KEM.OneCCA.inside (PK C K A H : Type) [Fintype PK] [Fintype C] [Fintype K] [Fintype A]
    [Fintype H] (q : KEMOneCCA.Port → ℕ) : Interface :=
  (Encapsulation.perPort PK C K (KEM.OneCCA.insideBudget q)).tensor (Evaluation A H (q .ro))

/-- The inside calls of `kem-1cca-real+ro` per procedure: one, at its own port. -/
def KEM.OneCCAReal.calls : KEMOneCCA.Port → Encapsulation.Port ⊕ Evaluation.Port → ℕ
  | .pk, .inl .publicKey => 1
  | .enc, .inl .encaps => 1
  | .dec, .inl .decaps => 1
  | .ro, .inr .eval => 1
  | _, _ => 0

/-- `kem-1cca-real+ro` calls each inside label at most `KEM.OneCCAReal.calls` times per
procedure. -/
lemma KEM.OneCCAReal.labelBounded :
    (KEM.OneCCAReal.body PK C K A H).LabelBounded KEM.OneCCAReal.calls := by
  intro s o u
  cases o <;> simp only [KEM.OneCCAReal.body] <;> cases s <;> dsimp only <;>
    repeat' (first
      | exact Program.labelCallBound_return _ _
      | (refine Program.labelCallBound_call _ _ _ (by decide) fun y => ?_)
      | split)

/-- The inside interface admits the per-label budget of `kem-1cca-real+ro`. -/
lemma KEM.OneCCAReal.admits (q : KEMOneCCA.Port → ℕ) :
    (KEM.OneCCA.inside PK C K A H q).AdmitsLabelBudget
      fun j => ∑ o, KEM.OneCCAReal.calls o j * q o := by
  refine ((portBudget_admitsLabelBudget _ _ _ _).tensor (queryBudget_admitsLabelBudget _ _ _
    (fun _ => q .ro) (by simp))).mono fun j => ?_
  rcases j with (_ | _ | _) | _ <;>
    simp [Finset.univ, Fintype.elems, KEM.OneCCAReal.calls, KEM.OneCCA.insideBudget]
  all_goals omega

/-- **`kem-1cca-real+ro` at per-port budgets.** -/
def KEM.OneCCAReal.perLabel (q : KEMOneCCA.Port → ℕ) :
    KEMOneCCA.perPort PK C K A H q ⟶ KEM.OneCCA.inside PK C K A H q :=
  Converter.ofLabelBoundedProgram (A := KEMOneCCA.perPort PK C K A H q)
    (B := KEM.OneCCA.inside PK C K A H q) none (KEM.OneCCAReal.body PK C K A H)
    (KEM.OneCCAReal.bound_spec PK C K A H) KEM.OneCCAReal.calls KEM.OneCCAReal.labelBounded q
    (fun _ hd => hd.2) (KEM.OneCCAReal.admits q)

variable [DecidableEq PK] [DecidableEq C] [Nonempty K]

/-- The inside calls of `kem-1cca-rand+ro` per procedure: its sources and `kem.publicKey()` once
each, `kem.decaps` once from `dec`, and the oracle once from `ro`. -/
def KEM.OneCCARand.calls :
    KEMOneCCA.Port → (Encapsulation.Port ⊕ Evaluation.Port) ⊕ (Unit ⊕ Unit) → ℕ
  | .pk, .inl (.inl .publicKey) => 1
  | .enc, .inl (.inl .publicKey) => 1
  | .dec, .inl (.inl .publicKey) => 1
  | .dec, .inl (.inl .decaps) => 1
  | .ro, .inl (.inr .eval) => 1
  | _, .inr _ => 1
  | _, _ => 0

/-- `kem-1cca-rand+ro` calls each inside label at most `KEM.OneCCARand.calls` times per
procedure. -/
lemma KEM.OneCCARand.labelBounded (ciphertexts : PK → Distribution.ProbDist C) :
    (KEM.OneCCARand.body PK C K A H ciphertexts).LabelBounded KEM.OneCCARand.calls := by
  intro s o u
  cases o <;> simp only [KEM.OneCCARand.body] <;> cases s <;> dsimp only <;>
    repeat' (first
      | exact Program.labelCallBound_return _ _
      | (refine Program.labelCallBound_call _ _ _ (by decide) fun y => ?_)
      | split)

/-- The inside interface of the program of `kem-1cca-rand+ro`: the KEM and the oracle beside its
sources. -/
abbrev KEM.OneCCARand.inside (PK C K A H : Type) [Fintype PK] [Fintype C] [Fintype K]
    [Fintype A] [Fintype H] [DecidableEq PK] [DecidableEq C] [Nonempty K]
    (ciphertexts : PK → Distribution.ProbDist C) (q : KEMOneCCA.Port → ℕ) : Interface :=
  (KEM.OneCCA.inside PK C K A H q).tensor
    ((Interface.source (lawType (KEM.OneCCARand.law1 PK C K A H ciphertexts))
        (KEM.OneCCARand.bound PK C K A H ciphertexts * ∑ i, q i)).tensor
      (Interface.source (lawType (KEM.OneCCARand.law2 PK C K A H ciphertexts))
        (KEM.OneCCARand.bound PK C K A H ciphertexts * ∑ i, q i)))

/-- The inside interface admits the per-label budget of `kem-1cca-rand+ro`. -/
lemma KEM.OneCCARand.admits (ciphertexts : PK → Distribution.ProbDist C)
    (q : KEMOneCCA.Port → ℕ) :
    (KEM.OneCCARand.inside PK C K A H ciphertexts q).AdmitsLabelBudget
      fun j => ∑ o, KEM.OneCCARand.calls o j * q o := by
  have hs : ∑ i, q i ≤ KEM.OneCCARand.bound PK C K A H ciphertexts * ∑ i, q i :=
    Nat.le_mul_of_pos_left _ (by norm_num [KEM.OneCCARand.bound])
  refine (((portBudget_admitsLabelBudget _ _ _ _).tensor (queryBudget_admitsLabelBudget _ _ _
    (fun _ => q .ro) (by simp))).tensor
      ((queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simpa using hs)).tensor
        (queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simpa using hs)))).mono
    fun j => ?_
  rcases j with ((_ | _ | _) | _) | (_ | _) <;>
    simp [Finset.univ, Fintype.elems, KEM.OneCCARand.calls, KEM.OneCCA.insideBudget]
  all_goals omega

/-- **`kem-1cca-rand+ro` at per-port budgets**: its program at the per-label call bound, beside
its sources. -/
def KEM.OneCCARand.perLabel (ciphertexts : PK → Distribution.ProbDist C)
    (q : KEMOneCCA.Port → ℕ) :
    KEMOneCCA.perPort PK C K A H q ⟶ KEM.OneCCA.inside PK C K A H q :=
  Converter.ofLabelBoundedProgram (A := KEMOneCCA.perPort PK C K A H q)
      (B := KEM.OneCCARand.inside PK C K A H ciphertexts q) none
      (KEM.OneCCARand.body PK C K A H ciphertexts)
      (KEM.OneCCARand.bound_spec PK C K A H ciphertexts)
      KEM.OneCCARand.calls (KEM.OneCCARand.labelBounded ciphertexts) q (fun _ hd => hd.2)
      (KEM.OneCCARand.admits ciphertexts q) ≫
    Interface.rightContext _ (KEM.OneCCARand.randomness PK C K A H ciphertexts
      (KEM.OneCCARand.bound PK C K A H ciphertexts * ∑ i, q i))

variable [DecidableEq A] [Nonempty H]

/-- **The systems of single-challenge IND$-CCA security of a KEM in the random-oracle model**
[1, §7]: `kem-1cca-real+ro` and `kem-1cca-rand+ro` on the real system, with the random ciphertexts
`ciphertexts pk` under each public key `pk`, at the budget `q` per port. -/
def KEM.OneCCA.systems (kem : (A → H) → KEM PK SK C K)
    (ciphertexts : PK → Distribution.ProbDist C) (q : KEMOneCCA.Port → ℕ) :
    Resource (KEMOneCCA.perPort PK C K A H q) × Resource (KEMOneCCA.perPort PK C K A H q) :=
  (KEM.OneCCAReal.perLabel q • KEM.RealRO kem (KEM.OneCCA.insideBudget q) (q .ro),
    KEM.OneCCARand.perLabel ciphertexts q • KEM.RealRO kem (KEM.OneCCA.insideBudget q) (q .ro))

/-- **Single-challenge IND$-CCA security of a KEM in the random-oracle model** within `error`:
against the admitted distinguishers, `kem-1cca-real+ro` substitutes for `kem-1cca-rand+ro`. -/
def KEM.OneCCA [AdmissibleDistinguishers] (kem : (A → H) → KEM PK SK C K)
    (ciphertexts : PK → Distribution.ProbDist C) {q : KEMOneCCA.Port → ℕ}
    (error : (KEMOneCCA.perPort PK C K A H q).inputDomain.DistinguisherBehavior → ENNReal) :
    Prop :=
  (KEM.OneCCA.systems kem ciphertexts q).1 ≃[error] (KEM.OneCCA.systems kem ciphertexts q).2

/-- **Fiberwise pushforwards with the same fibers**: moving the second sample of two independent
pairs with the same first law along maps that give it the same law for every possible first, gives
the same law. -/
lemma _root_.Probability.Distribution.fTransform_prod_fiber_congr {X Y₁ Y₂ Z : Type}
    (P : Distribution X) (Q₁ : Distribution Y₁) (Q₂ : Distribution Y₂) (g₁ : X → Y₁ → Z)
    (g₂ : X → Y₂ → Z)
    (h : ∀ x ∈ P.support, Distribution.fTransform (g₁ x) Q₁ = Distribution.fTransform (g₂ x) Q₂) :
    Distribution.fTransform (fun p => (p.1, g₁ p.1 p.2)) (Distribution.prod P Q₁) =
      Distribution.fTransform (fun p => (p.1, g₂ p.1 p.2)) (Distribution.prod P Q₂) := by
  classical
  ext ⟨x, z⟩
  rw [Distribution.fTransform_prod_fiber_apply, Distribution.fTransform_prod_fiber_apply]
  by_cases hx : x ∈ P.support
  · rw [h x hx]
  · rw [Finsupp.notMem_support_iff.mp hx, zero_mul, zero_mul]

/-- A label of an input of a history has an input in the history at that label. -/
lemma _root_.SystemAlgebra.restrict_ne_nil_of_mem {L : Type} {X : L → Type}
    {x : Σ l, X l} {xs : List (Σ l, X l)} (hx : x ∈ xs) : SystemAlgebra.restrict x.1 xs ≠ [] := by
  induction xs with
  | nil => simp at hx
  | cons y xs ih =>
    obtain ⟨l, a⟩ := y
    by_cases hl : l = x.1
    · subst hl
      simp
    · rw [SystemAlgebra.restrict_cons_ne hl]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact absurd rfl hl
      · exact ih hx

/-- **Functions agreeing at the labels with a budget** are the same resource at per-port
budgets. -/
lemma _root_.SystemAlgebra.Interface.Resource.ofFunction_congr_portBudget {L : Type}
    [Fintype L] {X Y : L → Type} [∀ l, Fintype (X l)] [∀ l, Fintype (Y l)] {q : L → ℕ}
    {f g : ∀ l, X l → Y l} (hfg : ∀ l, 0 < q l → f l = g l) :
    Resource.ofFunction (A := portBudget L X Y q) f = Resource.ofFunction g := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [Resource.ofFunction_mass, Resource.ofFunction_mass]
  by_cases hd : h = [] ∨ (portBudget L X Y q).domain (h.map Prod.fst)
  · -- Every query of an admitted history is at a label with a budget.
    have hpos : ∀ z ∈ h, f z.1.1 = g z.1.1 := fun z hz => by
      rcases hd with rfl | hd
      · simp at hz
      · refine hfg _ (lt_of_lt_of_le (List.length_pos_of_ne_nil ?_) (hd.2 z.1.1))
        exact SystemAlgebra.restrict_ne_nil_of_mem (List.mem_map_of_mem hz)
    have he : (∀ z ∈ h, z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩) ↔ ∀ z ∈ h, z.2 = ⟨z.1.1, g z.1.1 z.1.2⟩ :=
      forall₂_congr fun z hz => by rw [hpos z hz]
    by_cases hf : ∀ z ∈ h, z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩
    · rw [if_pos ⟨hd, hf⟩, if_pos ⟨hd, he.mp hf⟩]
    · rw [if_neg fun hc => hf hc.2, if_neg fun hc => hf (he.mpr hc.2)]
  · simp only [hd, false_and, if_false]

/-- **Sampling a resource that does not depend on the sample** is the resource. -/
lemma _root_.SystemAlgebra.Interface.Resource.sample_const {T : Interface} {L : Type}
    (P : Distribution L) [Distribution.IsProbability P] (R : Resource T) :
    Resource.sample P (fun _ => R) = R := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [Resource.sample_mass, ← Finset.sum_mul]
  have hw : ∑ l ∈ P.support, P l = 1 := (Distribution.IsProbability.isProbDist P).2
  rw [hw, one_mul]

omit [DecidableEq PK] [DecidableEq C] [Nonempty K] [DecidableEq A] [Nonempty H] in
/-- **An automaton whose initial law is a sampled state**, a function at each sample, is the
sampled function. -/
lemma _root_.SystemAlgebra.Interface.Resource.ofAutomaton_eq_sample_of_law {T : Interface}
    {S L : Type} (step : S → (i : T.I) → T.X i → S × T.Y i) (D : Distribution.ProbDist S)
    (P : Distribution L) [Distribution.IsProbability P] (init : L → S)
    (hD : D.1 = Distribution.fTransform init P) (f : L → ∀ i, T.X i → T.Y i)
    (h : ∀ l, automatonSystem step (init l) = functionSystem (f l)) :
    Resource.ofAutomaton T step D = Resource.sample P fun l => Resource.ofFunction (f l) := by
  obtain ⟨D, hDp⟩ := D
  change D = _ at hD
  subst hD
  exact Resource.ofAutomaton_eq_sample step P init f h

/-! ### The real system of a KEM against its sources -/

/-- The automaton of the real system of a KEM against its sources, with tables of `k` entries. -/
local notation "realStep(" kem ", " k ")" =>
  Program.combine (KEM.Real.body kem) (parallelStep (sourceStep (q := k) (KEM.Real.law1 kem))
    (sourceStep (q := k) (KEM.Real.law2 kem))) (KEM.Real.bound_spec kem)

omit [DecidableEq C] [Nonempty K] in
/-- The real system of a KEM against its sources: a first `publicKey()` reads the keys. -/
lemma KEM.Real.combine_publicKey_none (kem : KEM PK SK C K) {k : ℕ} (t₁ : Fin k → PK × SK)
    (c₁ : ℕ) (r : (Fin k → PK → C × K) × ℕ) :
    realStep(kem, k) (none, ((t₁, c₁), r)) .publicKey () =
      ((some (sourceEntry (KEM.Real.law1 kem) t₁ c₁), ((t₁, c₁ + 1), r)),
        (sourceEntry (KEM.Real.law1 kem) t₁ c₁).1) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, KEM.Real.body, callProg, returnProg, parallelStep, sourceStep,
      sourceEntry])

omit [DecidableEq C] [Nonempty K] in
/-- Once the keys are read, `publicKey()` returns the public key. -/
lemma KEM.Real.combine_publicKey_some (kem : KEM PK SK C K) {k : ℕ} (keys : PK × SK)
    (r : ((Fin k → PK × SK) × ℕ) × ((Fin k → PK → C × K) × ℕ)) :
    realStep(kem, k) (some keys, r) .publicKey () = ((some keys, r), keys.1) :=
  Program.combine_eq_of_invoke _ _ (n := 0) (by
    simp [Program.invoke, KEM.Real.body, returnProg])

omit [DecidableEq C] [Nonempty K] in
/-- A first `encaps()` reads the keys and the next encapsulations. -/
lemma KEM.Real.combine_encaps_none (kem : KEM PK SK C K) {k : ℕ} (t₁ : Fin k → PK × SK)
    (c₁ : ℕ) (t₂ : Fin k → PK → C × K) (c₂ : ℕ) :
    realStep(kem, k) (none, ((t₁, c₁), (t₂, c₂))) .encaps () =
      ((some (sourceEntry (KEM.Real.law1 kem) t₁ c₁), ((t₁, c₁ + 1), (t₂, c₂ + 1))),
        sourceEntry (KEM.Real.law2 kem) t₂ c₂ (sourceEntry (KEM.Real.law1 kem) t₁ c₁).1) :=
  Program.combine_eq_of_invoke _ _ (n := 2) (by
    simp [Program.invoke, KEM.Real.body, callProg, returnProg, parallelStep, sourceStep,
      sourceEntry]
    rfl)

omit [DecidableEq C] [Nonempty K] in
/-- Once the keys are read, `encaps()` reads the next encapsulations. -/
lemma KEM.Real.combine_encaps_some (kem : KEM PK SK C K) {k : ℕ} (keys : PK × SK)
    (r₁ : (Fin k → PK × SK) × ℕ) (t₂ : Fin k → PK → C × K) (c₂ : ℕ) :
    realStep(kem, k) (some keys, (r₁, (t₂, c₂))) .encaps () =
      ((some keys, (r₁, (t₂, c₂ + 1))), sourceEntry (KEM.Real.law2 kem) t₂ c₂ keys.1) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, KEM.Real.body, callProg, returnProg, parallelStep, sourceStep,
      sourceEntry])

omit [DecidableEq C] [Nonempty K] in
/-- A first `decaps(c)` reads the keys. -/
lemma KEM.Real.combine_decaps_none (kem : KEM PK SK C K) {k : ℕ} (t₁ : Fin k → PK × SK)
    (c₁ : ℕ) (r : (Fin k → PK → C × K) × ℕ) (c : C) :
    realStep(kem, k) (none, ((t₁, c₁), r)) .decaps c =
      ((some (sourceEntry (KEM.Real.law1 kem) t₁ c₁), ((t₁, c₁ + 1), r)),
        kem.decaps (sourceEntry (KEM.Real.law1 kem) t₁ c₁).2 c) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, KEM.Real.body, callProg, returnProg, parallelStep, sourceStep,
      sourceEntry])

omit [DecidableEq C] [Nonempty K] in
/-- Once the keys are read, `decaps(c)` decapsulates. -/
lemma KEM.Real.combine_decaps_some (kem : KEM PK SK C K) {k : ℕ} (keys : PK × SK)
    (r : ((Fin k → PK × SK) × ℕ) × ((Fin k → PK → C × K) × ℕ)) (c : C) :
    realStep(kem, k) (some keys, r) .decaps c = ((some keys, r), kem.decaps keys.2 c) :=
  Program.combine_eq_of_invoke _ _ (n := 0) (by
    simp [Program.invoke, KEM.Real.body, returnProg])

/-! ### `kem-1cca-real+ro` against the real system -/

/-- The automaton of `kem-1cca-real+ro` against `stepK` beside the oracle `RO`. -/
local notation "oneCCARealStep(" stepK ", " RO ")" =>
  Program.combine (KEM.OneCCAReal.body _ _ _ _ _)
    (parallelStep stepK (fun (_ : Unit) _ a => ((), RO a))) (KEM.OneCCAReal.bound_spec _ _ _ _ _)

section RealSteps

omit [DecidableEq PK] [DecidableEq C] [Nonempty K] [DecidableEq A] [Nonempty H]

variable {R : Type} (stepK : R → (j : Encapsulation.Port) → Encapsulation.Input C j →
    R × Encapsulation.Output PK C K j) (RO : A → H)

/-- `kem-1cca-real+ro` against a KEM: `pk()` is forwarded. -/
lemma KEM.OneCCAReal.combine_pk (s : Option (Option (C × K))) (r : R) :
    oneCCARealStep(stepK, RO) (s, (r, ())) .pk () =
      ((some (s.getD none), ((stepK r .publicKey ()).1, ())), (stepK r .publicKey ()).2) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    cases s <;> simp [Program.invoke, KEM.OneCCAReal.body, callProg, returnProg, parallelStep])

/-- `kem-1cca-real+ro` against a KEM: `enc()` returns the stored challenge. -/
lemma KEM.OneCCAReal.combine_enc_some (ck : C × K) (r : R) :
    oneCCARealStep(stepK, RO) (some (some ck), (r, ())) .enc () =
      ((some (some ck), (r, ())), ck) :=
  Program.combine_eq_of_invoke _ _ (n := 0) (by
    simp [Program.invoke, KEM.OneCCAReal.body, returnProg])

/-- `kem-1cca-real+ro` against a KEM: the first `enc()` stores an encapsulation. -/
lemma KEM.OneCCAReal.combine_enc_none {s : Option (Option (C × K))} (hs : s.getD none = none)
    (r : R) :
    oneCCARealStep(stepK, RO) (s, (r, ())) .enc () =
      ((some (some (stepK r .encaps ()).2), ((stepK r .encaps ()).1, ())),
        (stepK r .encaps ()).2) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    rcases s with _ | _ | _ <;>
      simp_all [Program.invoke, KEM.OneCCAReal.body, callProg, returnProg, parallelStep])

/-- `kem-1cca-real+ro` against a KEM: `dec(c)` is forwarded. -/
lemma KEM.OneCCAReal.combine_dec (s : Option (Option (C × K))) (r : R) (c : C) :
    oneCCARealStep(stepK, RO) (s, (r, ())) .dec c =
      ((some (s.getD none), ((stepK r .decaps c).1, ())), (stepK r .decaps c).2) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    cases s <;> simp [Program.invoke, KEM.OneCCAReal.body, callProg, returnProg, parallelStep])

/-- `kem-1cca-real+ro` against a KEM: `ro(a)` is forwarded to the oracle. -/
lemma KEM.OneCCAReal.combine_ro (s : Option (Option (C × K))) (r : R) (a : A) :
    oneCCARealStep(stepK, RO) (s, (r, ())) .ro a = ((some (s.getD none), (r, ())), RO a) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    cases s <;> simp [Program.invoke, KEM.OneCCAReal.body, callProg, returnProg, parallelStep])

end RealSteps

/-! ### `kem-1cca-rand+ro` against the real system -/

set_option hygiene false in
/-- The automaton of `kem-1cca-rand+ro` against `stepK` beside the oracle `RO`, and its sources
with tables of `k` entries. -/
local notation "oneCCARandStep(" ciphertexts ", " stepK ", " RO ", " k ")" =>
  Program.combine (KEM.OneCCARand.body PK C K A H ciphertexts)
    (parallelStep (parallelStep stepK (fun (_ : Unit) _ a => ((), RO a)))
      (parallelStep (sourceStep (q := k) (KEM.OneCCARand.law1 PK C K A H ciphertexts))
        (sourceStep (q := k) (KEM.OneCCARand.law2 PK C K A H ciphertexts))))
    (KEM.OneCCARand.bound_spec PK C K A H ciphertexts)

section RandSteps

omit [DecidableEq A] [Nonempty H]

variable {R : Type} (ciphertexts : PK → Distribution.ProbDist C)
  (stepK : R → (j : Encapsulation.Port) → Encapsulation.Input C j →
    R × Encapsulation.Output PK C K j) (RO : A → H) {k : ℕ}

set_option hygiene false in
/-- The challenge `(c*, K*)` of `kem-1cca-rand+ro` read from its tables. -/
local notation "challengeOf(" ciphertexts ", " t₃ ", " c₃ ", " t₄ ", " c₄ ")" =>
  (sourceEntry (KEM.OneCCARand.law1 PK C K A H ciphertexts) t₃ c₃,
    sourceEntry (KEM.OneCCARand.law2 PK C K A H ciphertexts) t₄ c₄)

/-- `kem-1cca-rand+ro` against a KEM: the first `pk()` reads the challenges and is forwarded. -/
lemma KEM.OneCCARand.combine_pk_none (r : R) (t₃ : Fin k → PK → C) (c₃ : ℕ) (t₄ : Fin k → K)
    (c₄ : ℕ) :
    oneCCARandStep(ciphertexts, stepK, RO, k) (none, ((r, ()), ((t₃, c₃), (t₄, c₄)))) .pk () =
      ((some challengeOf(ciphertexts, t₃, c₃, t₄, c₄),
        (((stepK r .publicKey ()).1, ()), ((t₃, c₃ + 1), (t₄, c₄ + 1)))),
        (stepK r .publicKey ()).2) :=
  Program.combine_eq_of_invoke _ _ (n := 3) (by
    simp [Program.invoke, KEM.OneCCARand.body, callProg, returnProg, parallelStep, sourceStep,
      sourceEntry]
    rfl)

/-- `kem-1cca-rand+ro` against a KEM: `pk()` is forwarded. -/
lemma KEM.OneCCARand.combine_pk_some (ck : (PK → C) × K) (r : R)
    (rs : ((Fin k → PK → C) × ℕ) × ((Fin k → K) × ℕ)) :
    oneCCARandStep(ciphertexts, stepK, RO, k) (some ck, ((r, ()), rs)) .pk () =
      ((some ck, (((stepK r .publicKey ()).1, ()), rs)), (stepK r .publicKey ()).2) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, KEM.OneCCARand.body, callProg, returnProg, parallelStep])

/-- `kem-1cca-rand+ro` against a KEM: the first `enc()` reads the challenges and returns the one
under the public key. -/
lemma KEM.OneCCARand.combine_enc_none (r : R) (t₃ : Fin k → PK → C) (c₃ : ℕ)
    (t₄ : Fin k → K) (c₄ : ℕ) :
    oneCCARandStep(ciphertexts, stepK, RO, k) (none, ((r, ()), ((t₃, c₃), (t₄, c₄)))) .enc () =
      ((some challengeOf(ciphertexts, t₃, c₃, t₄, c₄),
        (((stepK r .publicKey ()).1, ()), ((t₃, c₃ + 1), (t₄, c₄ + 1)))),
        (challengeOf(ciphertexts, t₃, c₃, t₄, c₄).1 (stepK r .publicKey ()).2,
          challengeOf(ciphertexts, t₃, c₃, t₄, c₄).2)) :=
  Program.combine_eq_of_invoke _ _ (n := 3) (by
    simp [Program.invoke, KEM.OneCCARand.body, callProg, returnProg, parallelStep, sourceStep,
      sourceEntry]
    rfl)

/-- `kem-1cca-rand+ro` against a KEM: `enc()` returns the challenge under the public key. -/
lemma KEM.OneCCARand.combine_enc_some (ck : (PK → C) × K) (r : R)
    (rs : ((Fin k → PK → C) × ℕ) × ((Fin k → K) × ℕ)) :
    oneCCARandStep(ciphertexts, stepK, RO, k) (some ck, ((r, ()), rs)) .enc () =
      ((some ck, (((stepK r .publicKey ()).1, ()), rs)), (ck.1 (stepK r .publicKey ()).2, ck.2)) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, KEM.OneCCARand.body, callProg, returnProg, parallelStep])

/-- `kem-1cca-rand+ro` against a KEM: the first `dec(c)` reads the challenges, answers `K*` at
`c*` and forwards `c` otherwise. -/
lemma KEM.OneCCARand.combine_dec_none (r : R) (t₃ : Fin k → PK → C) (c₃ : ℕ)
    (t₄ : Fin k → K) (c₄ : ℕ) (c : C) :
    oneCCARandStep(ciphertexts, stepK, RO, k) (none, ((r, ()), ((t₃, c₃), (t₄, c₄)))) .dec c =
      if c = challengeOf(ciphertexts, t₃, c₃, t₄, c₄).1 (stepK r .publicKey ()).2 then
        ((some challengeOf(ciphertexts, t₃, c₃, t₄, c₄),
          (((stepK r .publicKey ()).1, ()), ((t₃, c₃ + 1), (t₄, c₄ + 1)))),
          some challengeOf(ciphertexts, t₃, c₃, t₄, c₄).2)
      else
        ((some challengeOf(ciphertexts, t₃, c₃, t₄, c₄),
          (((stepK (stepK r .publicKey ()).1 .decaps c).1, ()), ((t₃, c₃ + 1), (t₄, c₄ + 1)))),
          (stepK (stepK r .publicKey ()).1 .decaps c).2) := by
  split_ifs with hc <;> simp only [sourceEntry, sourceStep] at hc
  · exact Program.combine_eq_of_invoke _ _ (n := 3) (by
      simp [Program.invoke, KEM.OneCCARand.body, callProg, returnProg, parallelStep, sourceStep,
        sourceEntry, hc]
      rfl)
  · exact Program.combine_eq_of_invoke _ _ (n := 4) (by
      simp [Program.invoke, KEM.OneCCARand.body, callProg, returnProg, parallelStep, sourceStep,
        sourceEntry, hc]
      rfl)

/-- `kem-1cca-rand+ro` against a KEM: `dec(c)` answers `K*` at `c*` and forwards `c`
otherwise. -/
lemma KEM.OneCCARand.combine_dec_some (ck : (PK → C) × K) (r : R)
    (rs : ((Fin k → PK → C) × ℕ) × ((Fin k → K) × ℕ)) (c : C) :
    oneCCARandStep(ciphertexts, stepK, RO, k) (some ck, ((r, ()), rs)) .dec c =
      if c = ck.1 (stepK r .publicKey ()).2 then
        ((some ck, (((stepK r .publicKey ()).1, ()), rs)), some ck.2)
      else
        ((some ck, (((stepK (stepK r .publicKey ()).1 .decaps c).1, ()), rs)),
          (stepK (stepK r .publicKey ()).1 .decaps c).2) := by
  split_ifs with hc
  · exact Program.combine_eq_of_invoke _ _ (n := 1) (by
      simp [Program.invoke, KEM.OneCCARand.body, callProg, returnProg, parallelStep, hc])
  · exact Program.combine_eq_of_invoke _ _ (n := 2) (by
      simp [Program.invoke, KEM.OneCCARand.body, callProg, returnProg, parallelStep, hc])

/-- `kem-1cca-rand+ro` against a KEM: the first `ro(a)` reads the challenges and is forwarded to
the oracle. -/
lemma KEM.OneCCARand.combine_ro_none (r : R) (t₃ : Fin k → PK → C) (c₃ : ℕ) (t₄ : Fin k → K)
    (c₄ : ℕ) (a : A) :
    oneCCARandStep(ciphertexts, stepK, RO, k) (none, ((r, ()), ((t₃, c₃), (t₄, c₄)))) .ro a =
      ((some challengeOf(ciphertexts, t₃, c₃, t₄, c₄), ((r, ()), ((t₃, c₃ + 1), (t₄, c₄ + 1)))),
        RO a) :=
  Program.combine_eq_of_invoke _ _ (n := 3) (by
    simp [Program.invoke, KEM.OneCCARand.body, callProg, returnProg, parallelStep, sourceStep,
      sourceEntry]
    rfl)

/-- `kem-1cca-rand+ro` against a KEM: `ro(a)` is forwarded to the oracle. -/
lemma KEM.OneCCARand.combine_ro_some (ck : (PK → C) × K) (r : R)
    (rs : ((Fin k → PK → C) × ℕ) × ((Fin k → K) × ℕ)) (a : A) :
    oneCCARandStep(ciphertexts, stepK, RO, k) (some ck, ((r, ()), rs)) .ro a =
      ((some ck, ((r, ()), rs)), RO a) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, KEM.OneCCARand.body, callProg, returnProg, parallelStep])

end RandSteps

/-! ### The converters on the real system as sampled functions -/

/-- The answers of `kem-1cca-real+ro` for the oracle `RO`, the keys and the challenge `ck`. -/
def KEM.OneCCAReal.answers (kem : (A → H) → KEM PK SK C K) (RO : A → H) (keys : PK × SK)
    (ck : C × K) : ∀ i, KEMOneCCA.Input C A i → KEMOneCCA.Output PK C K H i
  | .pk => fun _ => keys.1
  | .enc => fun _ => ck
  | .dec => fun c => (kem RO).decaps keys.2 c
  | .ro => fun a => RO a

/-- The answers of `kem-1cca-rand+ro` for the oracle `RO`, the keys and the challenge
`(c*, K*)`. -/
def KEM.OneCCARand.answers (kem : (A → H) → KEM PK SK C K) (RO : A → H) (keys : PK × SK)
    (cstar : C) (kstar : K) : ∀ i, KEMOneCCA.Input C A i → KEMOneCCA.Output PK C K H i
  | .pk => fun _ => keys.1
  | .enc => fun _ => (cstar, kstar)
  | .dec => fun c => if c = cstar then some kstar else (kem RO).decaps keys.2 c
  | .ro => fun a => RO a

omit [DecidableEq C] [Nonempty K] in
/-- **`kem-1cca-real+ro` on the real system is a sampled function**: the oracle, the keys and an
encapsulation under every public key, sampled once, the challenge being the one under the public
key. -/
lemma KEM.OneCCAReal.smul_realRO (kem : (A → H) → KEM PK SK C K) (q : KEMOneCCA.Port → ℕ) :
    KEM.OneCCAReal.perLabel q • KEM.RealRO kem (KEM.OneCCA.insideBudget q) (q .ro) =
      Resource.sample (Distribution.uniform (A → H)) fun RO =>
        Resource.sample (Distribution.prod (kem RO).gen.1 (kem RO).encapsulations.1) fun x =>
          Resource.ofFunction (A := KEMOneCCA.perPort PK C K A H q)
            (KEM.OneCCAReal.answers kem RO x.1 (x.2 x.1.1)) := by
  unfold KEM.RealRO
  rw [Resource.smul_sample]
  congr 1
  funext RO
  -- The KEM beside the oracle is one automaton reading the tables of its sources.
  rw [KEM.Real.perPort, KEM.Real.randomness, Resource.source, Resource.source,
    parallel_ofAutomaton, Converter.ofProgram_smul_ofAutomaton, Resource.ofFunction_eq_ofAutomaton,
    parallel_ofAutomaton, KEM.OneCCAReal.perLabel, Converter.ofLabelBoundedProgram,
    Interface.ofDDC_ofProgramOn_smul_ofAutomaton (A := KEMOneCCA.perPort PK C K A H q)
      (B := KEM.OneCCA.inside PK C K A H q) (hb := KEM.OneCCAReal.bound_spec PK C K A H)]
  -- The tables of the keys and of the encapsulations, and the answers on their first entries.
  let n := KEM.Real.bound (kem RO) * ∑ i, KEM.OneCCA.insideBudget q i
  let law₁ := KEM.Real.law1 (kem RO)
  let law₂ := KEM.Real.law2 (kem RO)
  let entries : (Fin n → PK × SK) × (Fin n → PK → C × K) → (PK × SK) × (PK → C × K) :=
    Prod.map (fun t => sourceEntry law₁ t 0) (fun t => sourceEntry law₂ t 0)
  refine (Resource.ofAutomaton_eq_sample_of_law _ _
    (Distribution.prod (Distribution.pi fun _ : Fin n => law₁.1)
      (Distribution.pi fun _ : Fin n => law₂.1))
    (fun t => ((none : Option (Option (C × K))),
      (((none : Option (PK × SK)), ((t.1, 0), (t.2, 0))), ()))) ?hinit
    (fun t => KEM.OneCCAReal.answers kem RO (entries t).1 ((entries t).2 (entries t).1.1))
    fun t => ?bisim).trans ?_
  · dsimp only
    rw [Distribution.ProbDist.single, Distribution.prod_single_right,
      ← Distribution.fTransform_prod, Distribution.fTransform_comp, Distribution.fTransform_comp,
      Distribution.fTransform_comp]
    rfl
  · -- The keys are read at the first query to the KEM, the encapsulations at the first challenge.
    rw [functionSystem_eq_automatonSystem]
    refine automatonSystem_eq_of_bisim _ (rel := fun (st : Option (Option (C × K)) ×
        (Option (PK × SK) × ((Fin n → PK × SK) × ℕ) × ((Fin n → PK → C × K) × ℕ)) × Unit)
        (_ : Unit) => st.2.1.2.1.1 = t.1 ∧ st.2.1.2.2.1 = t.2 ∧
          ((st.2.1.1 = none ∧ st.2.1.2.1.2 = 0) ∨
            (st.2.1.1 = some (entries t).1 ∧ st.2.1.2.1.2 = 1)) ∧
          ((st.1.getD none = none ∧ st.2.1.2.2.2 = 0) ∨
            (st.1.getD none = some ((entries t).2 (entries t).1.1) ∧ st.2.1.2.2.2 = 1 ∧
              st.2.1.1 = some (entries t).1))) ?_
      ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    rintro ⟨sC, ⟨sK, ⟨t₁', c₁⟩, ⟨t₂', c₂⟩⟩, ⟨⟩⟩ ⟨⟩ i x ⟨rfl, rfl, hK, hC⟩
    dsimp only at hK hC
    -- The challenge stays as it was at the queries other than the first challenge.
    have hC' : ((some (sC.getD none)).getD none = none ∧ c₂ = 0) ∨
        ((some (sC.getD none)).getD none = some ((entries t).2 (entries t).1.1) ∧ c₂ = 1 ∧
          sK = some (entries t).1) := hC
    cases i
    · -- `pk()`: the public key, reading the keys at the first query to the KEM.
      rw [KEM.OneCCAReal.combine_pk]
      rcases hK with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [KEM.Real.combine_publicKey_none]
        refine ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩, ?_⟩
        rcases hC' with hC' | ⟨-, -, h⟩
        · exact Or.inl hC'
        · exact absurd h (by simp)
      · rw [KEM.Real.combine_publicKey_some]
        exact ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩, hC'⟩
    · -- `enc()`: the stored challenge, or a first encapsulation.
      rcases hC with ⟨hC, rfl⟩ | ⟨hC, rfl, rfl⟩
      · rw [KEM.OneCCAReal.combine_enc_none _ _ hC]
        rcases hK with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [KEM.Real.combine_encaps_none]
          exact ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl, rfl⟩⟩
        · rw [KEM.Real.combine_encaps_some]
          exact ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl, rfl⟩⟩
      · obtain ⟨⟩ | ⟨⟨⟩ | ck⟩ := sC <;> simp only [Option.getD_none, Option.getD_some,
          reduceCtorEq, Option.some.injEq] at hC
        subst hC
        rw [KEM.OneCCAReal.combine_enc_some]
        refine ⟨rfl, rfl, rfl, ?_, Or.inr ⟨rfl, rfl, rfl⟩⟩
        rcases hK with ⟨h, -⟩ | hK
        · exact absurd h (by simp)
        · exact Or.inr hK
    · -- `dec(c)`: decapsulation, reading the keys at the first query to the KEM.
      rw [KEM.OneCCAReal.combine_dec]
      rcases hK with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [KEM.Real.combine_decaps_none]
        refine ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩, ?_⟩
        rcases hC' with hC' | ⟨-, -, h⟩
        · exact Or.inl hC'
        · exact absurd h (by simp)
      · rw [KEM.Real.combine_decaps_some]
        exact ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩, hC'⟩
    · -- `ro(a)`: the oracle.
      rw [KEM.OneCCAReal.combine_ro]
      exact ⟨rfl, rfl, rfl, hK, hC'⟩
  · -- The first entries of the tables have the laws of the keys and of the encapsulations.
    rw [← Resource.sample_fTransform entries _ (fun x => Resource.ofFunction
      (A := KEMOneCCA.perPort PK C K A H q) (KEM.OneCCAReal.answers kem RO x.1 (x.2 x.1.1)))]
    by_cases hk : 0 < n
    · refine Resource.sample_congr_law ?_ _
      rw [Distribution.fTransform_prod, sourceEntry_zero_law _ hk, sourceEntry_zero_law _ hk]
      rfl
    · -- Without a query to the KEM, only the oracle answers.
      have hq : ∀ l, 0 < q l → l = .ro := fun l hl => by
        have hb : 0 < KEM.Real.bound (kem RO) := by norm_num [KEM.Real.bound]
        cases l <;> simp_all [n, Finset.univ, Fintype.elems]
      have hconst : ∀ x : (PK × SK) × (PK → C × K), Resource.ofFunction
          (A := KEMOneCCA.perPort PK C K A H q) (KEM.OneCCAReal.answers kem RO x.1 (x.2 x.1.1)) =
          Resource.ofFunction (KEM.OneCCAReal.answers kem RO (Classical.choice law₁.nonempty)
            (Classical.choice law₂.nonempty (Classical.choice law₁.nonempty).1)) := fun x =>
        Resource.ofFunction_congr_portBudget fun l hl => by rw [hq l hl]; rfl
      simp only [hconst, Resource.sample_const]

/-- **`kem-1cca-rand+ro` on the real system is a sampled function**: the oracle, the keys, a
random ciphertext under every public key and a uniform key, sampled once, the challenge being the
ciphertext under the public key and the key. -/
lemma KEM.OneCCARand.smul_realRO (kem : (A → H) → KEM PK SK C K)
    (ciphertexts : PK → Distribution.ProbDist C) (q : KEMOneCCA.Port → ℕ) :
    KEM.OneCCARand.perLabel ciphertexts q • KEM.RealRO kem (KEM.OneCCA.insideBudget q) (q .ro) =
      Resource.sample (Distribution.uniform (A → H)) fun RO =>
        Resource.sample (Distribution.prod (Distribution.prod (kem RO).gen.1
            (Distribution.ProbDist.pi ciphertexts).1) (Distribution.uniform K)) fun x =>
          Resource.ofFunction (A := KEMOneCCA.perPort PK C K A H q)
            (KEM.OneCCARand.answers kem RO x.1.1 (x.1.2 x.1.1.1) x.2) := by
  unfold KEM.RealRO
  rw [Resource.smul_sample]
  congr 1
  funext RO
  -- The KEM beside the oracle and the sources of the converter are one automaton reading the
  -- tables of the sources.
  rw [KEM.OneCCARand.perLabel, Interface.comp_smul, Interface.attach_rightContext,
    KEM.Real.perPort, KEM.Real.randomness, Resource.source, Resource.source,
    parallel_ofAutomaton, Converter.ofProgram_smul_ofAutomaton, Resource.ofFunction_eq_ofAutomaton,
    parallel_ofAutomaton, KEM.OneCCARand.randomness, Resource.source, Resource.source,
    parallel_ofAutomaton, parallel_ofAutomaton, Converter.ofLabelBoundedProgram,
    Interface.ofDDC_ofProgramOn_smul_ofAutomaton (A := KEMOneCCA.perPort PK C K A H q)
      (B := KEM.OneCCARand.inside PK C K A H ciphertexts q)
      (hb := KEM.OneCCARand.bound_spec PK C K A H ciphertexts)]
  -- The tables of the keys, of the encapsulations and of the challenges, and the answers on
  -- their first entries.
  let n := KEM.Real.bound (kem RO) * ∑ i, KEM.OneCCA.insideBudget q i
  let m := KEM.OneCCARand.bound PK C K A H ciphertexts * ∑ i, q i
  let law₁ := KEM.Real.law1 (kem RO)
  let law₂ := KEM.Real.law2 (kem RO)
  let law₃ := KEM.OneCCARand.law1 PK C K A H ciphertexts
  let law₄ := KEM.OneCCARand.law2 PK C K A H ciphertexts
  let entries : ((Fin n → PK × SK) × (Fin n → PK → C × K)) × ((Fin m → PK → C) × (Fin m → K)) →
      ((PK × SK) × (PK → C)) × K :=
    fun t => ((sourceEntry law₁ t.1.1 0, sourceEntry law₃ t.2.1 0), sourceEntry law₄ t.2.2 0)
  refine (Resource.ofAutomaton_eq_sample_of_law _ _
    (Distribution.prod (Distribution.prod (Distribution.pi fun _ : Fin n => law₁.1)
      (Distribution.pi fun _ : Fin n => law₂.1))
      (Distribution.prod (Distribution.pi fun _ : Fin m => law₃.1)
        (Distribution.pi fun _ : Fin m => law₄.1)))
    (fun t => ((none : Option ((PK → C) × K)), ((((none : Option (PK × SK)),
      ((t.1.1, 0), (t.1.2, 0))), ()), ((t.2.1, 0), (t.2.2, 0))))) ?hinit
    (fun t => KEM.OneCCARand.answers kem RO (entries t).1.1 ((entries t).1.2 (entries t).1.1.1)
      (entries t).2)
    fun t => ?bisim).trans ?_
  · dsimp only
    simp only [Distribution.ProbDist.single, Distribution.prod_single_right,
      ← Distribution.fTransform_prod, Distribution.fTransform_comp]
    rfl
  · -- The keys are read at the first query to the KEM, the challenges at the first query.
    rw [functionSystem_eq_automatonSystem]
    refine automatonSystem_eq_of_bisim _ (rel := fun (st : Option ((PK → C) × K) ×
        ((Option (PK × SK) × ((Fin n → PK × SK) × ℕ) × ((Fin n → PK → C × K) × ℕ)) × Unit) ×
          (((Fin m → PK → C) × ℕ) × ((Fin m → K) × ℕ))) (_ : Unit) =>
        st.2.1.1.2.1.1 = t.1.1 ∧ st.2.1.1.2.2 = (t.1.2, 0) ∧
          ((st.2.1.1.1 = none ∧ st.2.1.1.2.1.2 = 0) ∨
            (st.2.1.1.1 = some (entries t).1.1 ∧ st.2.1.1.2.1.2 = 1)) ∧
          st.2.2.1.1 = t.2.1 ∧ st.2.2.2.1 = t.2.2 ∧
          ((st.1 = none ∧ st.2.2.1.2 = 0 ∧ st.2.2.2.2 = 0) ∨
            (st.1 = some ((entries t).1.2, (entries t).2) ∧ st.2.2.1.2 = 1 ∧ st.2.2.2.2 = 1))) ?_
      ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩, rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
    rintro ⟨sC, ⟨⟨sK, ⟨t₁', c₁⟩, ⟨t₂', c₂⟩⟩, ⟨⟩⟩, ⟨t₃', c₃⟩, ⟨t₄', c₄⟩⟩ ⟨⟩ i x
      ⟨rfl, h₂, hK, rfl, rfl, hC⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₂
    dsimp only at hK hC
    cases i
    · -- `pk()`: the public key.
      rcases hC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      on_goal 1 => rw [KEM.OneCCARand.combine_pk_none]
      on_goal 2 => rw [KEM.OneCCARand.combine_pk_some]
      all_goals rcases hK with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals first
        | rw [KEM.Real.combine_publicKey_none]
        | rw [KEM.Real.combine_publicKey_some]
      all_goals exact ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩, rfl, rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩
    · -- `enc()`: the challenge under the public key.
      rcases hC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      on_goal 1 => rw [KEM.OneCCARand.combine_enc_none]
      on_goal 2 => rw [KEM.OneCCARand.combine_enc_some]
      all_goals rcases hK with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals first
        | rw [KEM.Real.combine_publicKey_none]
        | rw [KEM.Real.combine_publicKey_some]
      all_goals exact ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩, rfl, rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩
    · -- `dec(c)`: `K*` at `c*`, decapsulation otherwise.
      rcases hC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      on_goal 1 => rw [KEM.OneCCARand.combine_dec_none]
      on_goal 2 => rw [KEM.OneCCARand.combine_dec_some]
      all_goals rcases hK with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals first
        | rw [KEM.Real.combine_publicKey_none]
        | rw [KEM.Real.combine_publicKey_some]
      all_goals split_ifs with hc
      all_goals first
        | exact ⟨(if_pos hc).symm, rfl, rfl, Or.inr ⟨rfl, rfl⟩, rfl, rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩
        | (rw [KEM.Real.combine_decaps_some]
           exact ⟨(if_neg hc).symm, rfl, rfl, Or.inr ⟨rfl, rfl⟩, rfl, rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩)
    · -- `ro(a)`: the oracle.
      rcases hC with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      on_goal 1 => rw [KEM.OneCCARand.combine_ro_none]
      on_goal 2 => rw [KEM.OneCCARand.combine_ro_some]
      all_goals exact ⟨rfl, rfl, rfl, hK, rfl, rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩
  · -- The first entries of the tables have the laws of the keys and of the challenges.
    rw [← Resource.sample_fTransform entries _ (fun x => Resource.ofFunction
      (A := KEMOneCCA.perPort PK C K A H q) (KEM.OneCCARand.answers kem RO x.1.1 (x.1.2 x.1.1.1)
        x.2))]
    by_cases hm : 0 < m
    swap
    · exact Resource.eq_of_not_domain fun h hd => hm
        (Nat.mul_pos (by norm_num [KEM.OneCCARand.bound]) (bound_pos_of_domain hd))
    by_cases hk : 0 < n
    · refine Resource.sample_congr_law ?_ _
      rw [show entries = (fun p => ((p.1.1, p.2.1), p.2.2)) ∘ Prod.map (Prod.map
          (fun t => sourceEntry law₁ t 0) (fun t => sourceEntry law₂ t 0))
          (Prod.map (fun t => sourceEntry law₃ t 0) (fun t => sourceEntry law₄ t 0)) from rfl,
        ← Distribution.fTransform_comp, Distribution.fTransform_prod, Distribution.fTransform_prod,
        Distribution.fTransform_prod, sourceEntry_zero_law _ hk, sourceEntry_zero_law _ hk,
        sourceEntry_zero_law _ hm, sourceEntry_zero_law _ hm,
        show (fun p : ((PK × SK) × (PK → C × K)) × ((PK → C) × K) => ((p.1.1, p.2.1), p.2.2)) =
          (fun p => ((p.1, p.2.1), p.2.2)) ∘ Prod.map Prod.fst id from rfl,
        ← Distribution.fTransform_comp, Distribution.fTransform_prod, Distribution.fTransform_id,
        Distribution.fTransform_fst_prod, law₂.2.2, one_smul, Distribution.fTransform_assoc_prod]
      rfl
    · -- Without a query to the KEM, only the oracle answers.
      have hq : ∀ l, 0 < q l → l = .ro := fun l hl => by
        have hb : 0 < KEM.Real.bound (kem RO) := by norm_num [KEM.Real.bound]
        cases l <;> simp_all [n, Finset.univ, Fintype.elems]
      have hconst : ∀ x : ((PK × SK) × (PK → C)) × K, Resource.ofFunction
          (A := KEMOneCCA.perPort PK C K A H q)
            (KEM.OneCCARand.answers kem RO x.1.1 (x.1.2 x.1.1.1) x.2) =
          Resource.ofFunction (KEM.OneCCARand.answers kem RO
            (Classical.choice law₁.nonempty)
            (Classical.choice law₃.nonempty (Classical.choice law₁.nonempty).1)
            (Classical.choice law₄.nonempty)) := fun x =>
        Resource.ofFunction_congr_portBudget fun l hl => by rw [hq l hl]; rfl
      simp only [hconst, Resource.sample_const]

end

end Commons

namespace ProofLadders.RSAKEM

open Commons Probability SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface CategoryTheory
open scoped SystemAlgebra SystemAlgebra.DSL

/-- The interface of the RSA-KEM libraries at the budget `q` per port: the public keys `(N, e)`,
the ciphertexts and the oracle's inputs in the residues, and the keys `K`. -/
abbrev OneCCA (bits : ℕ) (K : Type) [Fintype K] (q : KEMOneCCA.Port → ℕ) : Interface :=
  KEMOneCCA.perPort (RSA.Residue bits × RSA.Residue bits) (RSA.Residue bits) K (RSA.Residue bits)
    K q

variable {bits : ℕ} {K : Type} [Fintype K] [Nonempty K] [DecidableEq K]

/-- **Encapsulation** on the randomness `R`: `c := R^e mod N` and `K := RO(R)`. -/
def encapsulate (key : RSA.Key bits) (RO : RSA.Residue bits → K)
    (R : RSA.Residue bits) : RSA.Residue bits × K :=
  (key.pow R key.e.val, RO R)

/-- **Decapsulation**: `RO(c^d mod N)` for a residue `c` modulo `N`, and `⊥` otherwise. -/
def decapsulate (key : RSA.Key bits) (RO : RSA.Residue bits → K)
    (c : RSA.Residue bits) : Option K :=
  if c.val < key.N.val then some (RO (key.pow c key.d.val)) else none

noncomputable section

/-- **RSA-KEM** [1, §7] with the oracle `RO`: `(N, e, d) := RSA.KeyGen()`, `pk = (N, e)` and
`sk = (N, d)`; `Encaps(N, e)` samples `R ← ℤ_N` and returns `(R^e mod N, RO(R))`, and
`Decaps((N, d), c)` is `RO(c^d mod N)` for a residue `c` modulo `N`, and `⊥` otherwise. -/
def scheme (K : Type) (keyGen : Distribution.ProbDist (RSA.Key bits))
    (RO : RSA.Residue bits → K) :
    KEM (RSA.Residue bits × RSA.Residue bits) (RSA.Residue bits × RSA.Residue bits)
      (RSA.Residue bits) K where
  gen := Distribution.ProbDist.map (fun key => ((key.N, key.e), (key.N, key.d))) keyGen
  encaps pk :=
    Distribution.ProbDist.map (fun R => (RSA.powMod pk.1 pk.2 R, RO R)) (RSA.residue pk.1)
  decaps sk c := if c.val < sk.1.val then some (RO (RSA.powMod sk.1 sk.2 c)) else none

/-- **The random ciphertexts of RSA-KEM**: uniform in `ℤ_N` under the public key `(N, e)`. -/
def ciphertexts (pk : RSA.Residue bits × RSA.Residue bits) :
    Distribution.ProbDist (RSA.Residue bits) :=
  RSA.residue pk.1

-- `kem-1cca-real+ro`: `(N, e, d) := RSA.KeyGen()`, `(c*, K*) := Encaps(N, e)`; `pk()` returns
-- `(N, e)`, `enc()` returns `(c*, K*)`, `dec(c)` returns `Decaps(c)` and `ro(A)` returns
-- `RO(A)`.
system Real(K : Type) [Fintype K] [Nonempty K] [DecidableEq K] (keyGen : Distribution.ProbDist (RSA.Key bits)) : KEMOneCCA (RSA.Residue bits × RSA.Residue bits) (RSA.Residue bits) K (RSA.Residue bits) K
  initialize
    key ←$ keyGen
    Rs ←$ RSA.residues (bits := bits)
    RO ←$ 𝒰[RSA.Residue bits → K]
  on pk() → RSA.Residue bits × RSA.Residue bits
    return (key.N, key.e)
  on enc() → RSA.Residue bits × K
    return encapsulate key RO (Rs key.N)
  on dec(c : RSA.Residue bits) → Option K
    return decapsulate key RO c
  on ro(A : RSA.Residue bits) → K
    return RO A

-- `kem-1cca-rand+ro`: `(N, e, d) := RSA.KeyGen()`, `c* ← ℤ_N`, `K* ← {0,1}^λ`; `dec(c*)`
-- returns `K*`, and otherwise as `kem-1cca-real+ro`.
system Rand(K : Type) [Fintype K] [Nonempty K] [DecidableEq K] (keyGen : Distribution.ProbDist (RSA.Key bits)) : KEMOneCCA (RSA.Residue bits × RSA.Residue bits) (RSA.Residue bits) K (RSA.Residue bits) K
  initialize
    key ←$ keyGen
    cs ←$ RSA.residues (bits := bits)
    Kstar ←$ 𝒰[K]
    RO ←$ 𝒰[RSA.Residue bits → K]
  on pk() → RSA.Residue bits × RSA.Residue bits
    return (key.N, key.e)
  on enc() → RSA.Residue bits × K
    return (cs key.N, Kstar)
  on dec(c : RSA.Residue bits) → Option K
    if c = cs key.N
      return some Kstar
    else
      return decapsulate key RO c
  on ro(A : RSA.Residue bits) → K
    return RO A

end

/-! ## The reduction

The reduction `𝓡` takes `(N, e, Y)` from `rsa.challenge()` on every query, and answers from a
uniform table `T` and a uniform key `K*` it samples once. It calls the source and
`rsa.challenge()` at most once per invocation and `rsa.check` at most once per oracle query, so it
is typed at per-label inside budgets (`Interface.Converter.ofLabelBoundedProgram`). -/

noncomputable section

-- `𝓡`: `(N, e, Y) := rsa.challenge()`; `pk()` returns `(N, e)`; `enc()` returns `(Y, K*)`;
-- `dec(c)` returns `K*` at `c = Y`, `⊥` at a non-residue and `T(c)` otherwise; `ro(A)` at a
-- residue returns `K*` if `rsa.check(A)` and `T(A^e mod N)` otherwise, and `T(A)` otherwise.
converter 𝓡(bits : ℕ) (K : Type) [Fintype K] [Nonempty K] [DecidableEq K] : KEMOneCCA (RSA.Residue bits × RSA.Residue bits) (RSA.Residue bits) K (RSA.Residue bits) K
  inside rsa : RSAChallenge bits
  initialize
    TK ←$ 𝒰[(RSA.Residue bits → K) × K]
  on pk() → RSA.Residue bits × RSA.Residue bits
    (N, e, _Y) ← rsa.challenge()
    return (N, e)
  on enc() → RSA.Residue bits × K
    (_N, _e, Y) ← rsa.challenge()
    return (Y, TK.2)
  on dec(c : RSA.Residue bits) → Option K
    (N, _e, Y) ← rsa.challenge()
    if c = Y
      return some TK.2
    else
      if c.val < N.val
        return some (TK.1 c)
      else
        return none
  on ro(A : RSA.Residue bits) → K
    (N, e, _Y) ← rsa.challenge()
    if A.val < N.val
      found ← rsa.check(A)
      if found
        return TK.2
      else
        return TK.1 (RSA.powMod N e A)
    else
      return TK.1 A

/-- The inside calls of `𝓡` per procedure: the source and `rsa.challenge()` once each, and
`rsa.check` once from `ro`. -/
def 𝓡.calls : KEMOneCCA.Port → RSAChallenge.Port ⊕ Unit → ℕ
  | .ro, _ => 1
  | _, .inl .check => 0
  | _, _ => 1

/-- The reduction calls each inside label at most `𝓡.calls` times per procedure. -/
lemma 𝓡.labelBounded : (𝓡.body bits K).LabelBounded 𝓡.calls := by
  intro s o u
  cases o <;> simp only [𝓡.body] <;> cases s <;> dsimp only <;>
    repeat' (first
      | exact Program.labelCallBound_return _ _
      | (refine Program.labelCallBound_call _ _ _ (by decide) fun y => ?_)
      | split)

/-- The inside budget of the reduction: `rsa.challenge()` once per query and `rsa.check` once per
oracle query. -/
abbrev insideBudget (q : KEMOneCCA.Port → ℕ) : RSAChallenge.Port → ℕ
  | .challenge => q .pk + q .enc + q .dec + q .ro
  | .check => q .ro

/-- The inside interface of the program of `𝓡`: the RSA library beside the source. -/
abbrev 𝓡.inside (bits : ℕ) (K : Type) [Fintype K] [Nonempty K] [DecidableEq K]
    (q : KEMOneCCA.Port → ℕ) : Interface :=
  (RSAChallenge.perPort bits (insideBudget q)).tensor
    (Interface.source (lawType (𝓡.law1 bits K)) (𝓡.bound bits K * ∑ i, q i))

/-- The inside interface admits the per-label budget of `𝓡`. -/
lemma 𝓡.admits (q : KEMOneCCA.Port → ℕ) :
    (𝓡.inside bits K q).AdmitsLabelBudget fun j => ∑ o, 𝓡.calls o j * q o := by
  refine ((portBudget_admitsLabelBudget _ _ _ _).tensor (queryBudget_admitsLabelBudget _ _ _
    (fun _ => ∑ i, q i) ?_)).mono fun j => ?_
  · simpa using Nat.le_mul_of_pos_left _ (by norm_num [𝓡.bound])
  · rcases j with (_ | _) | _ <;> simp [Finset.univ, Fintype.elems, 𝓡.calls, insideBudget]
    all_goals omega

/-- **The reduction at per-port budgets**: the program of `𝓡` at the per-label call bound
`𝓡.calls`, beside its source. -/
def 𝓡.perLabel (q : KEMOneCCA.Port → ℕ) :
    OneCCA bits K q ⟶ RSAChallenge.perPort bits (insideBudget q) :=
  Converter.ofLabelBoundedProgram (A := OneCCA bits K q)
      (B := 𝓡.inside bits K q) none (𝓡.body bits K) (𝓡.bound_spec bits K)
      𝓡.calls 𝓡.labelBounded q (fun _ hd => hd.2) (𝓡.admits q) ≫
    Interface.rightContext _ (𝓡.randomness bits K (𝓡.bound bits K * ∑ i, q i))

end

noncomputable section

/-! ## Sampled functions

The key, `R*` and the oracle are sampled once and decapsulation is deterministic, so both
libraries are sampled functions, as are `rsa-real` and `rsa-fake` (`RSA.Real.sampled`). In
`kem-1cca-rand+ro` the uniform `c*` is `R*^e` for a uniform `R*`: by correctness `x ↦ x^e`
permutes `ℤ_N`, and the uniform law on `ℤ_N` re-indexed by a bijection is uniform. -/

/-- **`kem-1cca-real+ro` as a sampled function**: the key, the residues `R*` and the oracle
sampled once. -/
def Real.sampled (K : Type) [Fintype K] [Nonempty K] [DecidableEq K]
    (keyGen : Distribution.ProbDist (RSA.Key bits))
    {q : KEMOneCCA.Port → ℕ} : Resource (OneCCA bits K q) :=
  Resource.sample (Distribution.prod (Distribution.prod keyGen.1 (RSA.residues (bits := bits)).1)
      (Distribution.uniform (RSA.Residue bits → K))) fun x =>
    Resource.ofFunction fun
      | .pk => fun _ => (x.1.1.N, x.1.1.e)
      | .enc => fun _ => encapsulate x.1.1 x.2 (x.1.2 x.1.1.N)
      | .dec => fun c => decapsulate x.1.1 x.2 c
      | .ro => fun A => x.2 A

/-- **`kem-1cca-rand+ro` as a sampled function**: the key, the residues `c*`, the key `K*` and
the oracle sampled once. -/
def Rand.sampled (K : Type) [Fintype K] [Nonempty K] [DecidableEq K]
    (keyGen : Distribution.ProbDist (RSA.Key bits))
    {q : KEMOneCCA.Port → ℕ} : Resource (OneCCA bits K q) :=
  Resource.sample (Distribution.prod (Distribution.prod (Distribution.prod keyGen.1
      (RSA.residues (bits := bits)).1) (Distribution.uniform K))
      (Distribution.uniform (RSA.Residue bits → K))) fun x =>
    Resource.ofFunction fun
      | .pk => fun _ => (x.1.1.1.N, x.1.1.1.e)
      | .enc => fun _ => (x.1.1.2 x.1.1.1.N, x.1.2)
      | .dec => fun c =>
        if c = x.1.1.2 x.1.1.1.N then some x.1.2 else decapsulate x.1.1.1 x.2 c
      | .ro => fun A => x.2 A

/-- `kem-1cca-real+ro` is its sampled function. -/
lemma Real.perPort_eq_sampled (K : Type) [Fintype K] [Nonempty K] [DecidableEq K]
    (keyGen : Distribution.ProbDist (RSA.Key bits))
    (q : KEMOneCCA.Port → ℕ) :
    Real.perPort K keyGen (budget := q) = Real.sampled K keyGen := by
  -- The answers on the key, the residues `R*` and the oracle, and on them as the system stores
  -- them.
  let sampled : (RSA.Key bits × (RSA.Residue bits → RSA.Residue bits)) ×
      (RSA.Residue bits → K) →
      ∀ i, (OneCCA bits K q).X i → (OneCCA bits K q).Y i := fun x => fun
    | .pk => fun _ => (x.1.1.N, x.1.1.e)
    | .enc => fun _ => encapsulate x.1.1 x.2 (x.1.2 x.1.1.N)
    | .dec => fun c => decapsulate x.1.1 x.2 c
    | .ro => fun A => x.2 A
  let real : RSA.Key bits × (RSA.Residue bits → RSA.Residue bits) ×
      (RSA.Residue bits → K) →
      ∀ i, (OneCCA bits K q).X i → (OneCCA bits K q).Y i :=
    fun x => sampled ((x.1, x.2.1), x.2.2)
  let n := Real.bound K keyGen * ∑ i, q i
  let entries : (Fin n → RSA.Key bits) × (Fin n → RSA.Residue bits → RSA.Residue bits) ×
      (Fin n → RSA.Residue bits → K) →
      RSA.Key bits × (RSA.Residue bits → RSA.Residue bits) × (RSA.Residue bits → K) :=
    Prod.map (fun t => sourceEntry (Real.law1 K keyGen) t 0)
      (Prod.map (fun t => sourceEntry (Real.law2 K keyGen) t 0)
        (fun t => sourceEntry (Real.law3 K keyGen) t 0))
  -- The system reads its three sources at the first invocation.
  rw [Real.perPort, Real.randomness, Resource.source, Resource.source, Resource.source,
    parallel_ofAutomaton, parallel_ofAutomaton,
    Converter.ofProgram_smul_ofAutomaton_eq_sample (A := OneCCA bits K q) _ _ _ _ _ _
      (Distribution.prod (Distribution.pi fun _ => (Real.law1 K keyGen).1)
        (Distribution.prod (Distribution.pi fun _ => (Real.law2 K keyGen).1)
          (Distribution.pi fun _ => (Real.law3 K keyGen).1)))
      (fun t => ((t.1, 0), ((t.2.1, 0), (t.2.2, 0))))
      (by
        change _ = Distribution.fTransform (Prod.map (fun t => (t, 0))
          (Prod.map (fun t => (t, 0)) (fun t => (t, 0)))) _
        rw [Distribution.fTransform_prod, Distribution.fTransform_prod])
      (fun t => real (entries t))]
  · rw [← Resource.sample_fTransform (A := OneCCA bits K q) entries _
      (fun x => Resource.ofFunction (real x)), Real.sampled,
      Resource.sample_congr_law (P' := Distribution.fTransform (fun p => ((p.1, p.2.1), p.2.2))
        (Distribution.prod keyGen.1 (Distribution.prod (RSA.residues (bits := bits)).1
          (Distribution.uniform (RSA.Residue bits → K)))))
        (Distribution.fTransform_assoc_prod _ _ _).symm]
    conv_rhs => rw [Resource.sample_fTransform]
    by_cases hk : 0 < n
    · have law : Distribution.fTransform entries
          (Distribution.prod (Distribution.pi fun _ => (Real.law1 K keyGen).1)
            (Distribution.prod (Distribution.pi fun _ => (Real.law2 K keyGen).1)
              (Distribution.pi fun _ => (Real.law3 K keyGen).1))) =
          Distribution.prod keyGen.1 (Distribution.prod (RSA.residues (bits := bits)).1
            (Distribution.uniform (RSA.Residue bits → K))) := by
        rw [Distribution.fTransform_prod, Distribution.fTransform_prod, sourceEntry_zero_law _ hk,
          sourceEntry_zero_law _ hk, sourceEntry_zero_law _ hk]
        rfl
      exact Resource.sample_congr_law law _
    · exact Resource.eq_of_not_domain fun h hd => hk
        (Nat.mul_pos (by norm_num [Real.bound]) (bound_pos_of_domain hd))
  · rintro ⟨t₁, t₂, t₃⟩
    refine automatonSystem_of_stored _ real ((t₁, 0), ((t₂, 0), (t₃, 0))) (entries (t₁, t₂, t₃))
      (fun i x => ⟨((t₁, 1), ((t₂, 1), (t₃, 1))), ?_⟩) (fun r i x => ⟨r, ?_⟩)
    · refine Program.combine_eq_of_invoke _ _ (n := 3) ?_
      cases i <;> simp [Program.invoke, Real.body, callProg, returnProg, parallelStep,
        sourceStep, sourceEntry, real, sampled, entries, n]
    · refine Program.combine_eq_of_invoke _ _ (n := 0) ?_
      cases i <;> simp [Program.invoke, Real.body, returnProg, real, sampled]

/-- `kem-1cca-rand+ro` is its sampled function. -/
lemma Rand.perPort_eq_sampled (K : Type) [Fintype K] [Nonempty K] [DecidableEq K]
    (keyGen : Distribution.ProbDist (RSA.Key bits))
    (q : KEMOneCCA.Port → ℕ) :
    Rand.perPort K keyGen (budget := q) = Rand.sampled K keyGen := by
  -- As `Real.perPort_eq_sampled`, with four sources.
  let sampled : ((RSA.Key bits × (RSA.Residue bits → RSA.Residue bits)) × K) ×
      (RSA.Residue bits → K) →
      ∀ i, (OneCCA bits K q).X i → (OneCCA bits K q).Y i := fun x => fun
    | .pk => fun _ => (x.1.1.1.N, x.1.1.1.e)
    | .enc => fun _ => (x.1.1.2 x.1.1.1.N, x.1.2)
    | .dec => fun c =>
      if c = x.1.1.2 x.1.1.1.N then some x.1.2 else decapsulate x.1.1.1 x.2 c
    | .ro => fun A => x.2 A
  let rand : RSA.Key bits × (RSA.Residue bits → RSA.Residue bits) × K ×
      (RSA.Residue bits → K) →
      ∀ i, (OneCCA bits K q).X i → (OneCCA bits K q).Y i :=
    fun x => sampled (((x.1, x.2.1), x.2.2.1), x.2.2.2)
  let n := Rand.bound K keyGen * ∑ i, q i
  let entries : (Fin n → RSA.Key bits) × (Fin n → RSA.Residue bits → RSA.Residue bits) ×
      (Fin n → K) × (Fin n → RSA.Residue bits → K) →
      RSA.Key bits × (RSA.Residue bits → RSA.Residue bits) × K ×
        (RSA.Residue bits → K) :=
    Prod.map (fun t => sourceEntry (Rand.law1 K keyGen) t 0)
      (Prod.map (fun t => sourceEntry (Rand.law2 K keyGen) t 0)
        (Prod.map (fun t => sourceEntry (Rand.law3 K keyGen) t 0)
          (fun t => sourceEntry (Rand.law4 K keyGen) t 0)))
  rw [Rand.perPort, Rand.randomness, Resource.source, Resource.source, Resource.source,
    Resource.source, parallel_ofAutomaton, parallel_ofAutomaton, parallel_ofAutomaton,
    Converter.ofProgram_smul_ofAutomaton_eq_sample (A := OneCCA bits K q) _ _ _ _ _ _
      (Distribution.prod (Distribution.pi fun _ => (Rand.law1 K keyGen).1)
        (Distribution.prod (Distribution.pi fun _ => (Rand.law2 K keyGen).1)
          (Distribution.prod (Distribution.pi fun _ => (Rand.law3 K keyGen).1)
            (Distribution.pi fun _ => (Rand.law4 K keyGen).1))))
      (fun t => ((t.1, 0), ((t.2.1, 0), ((t.2.2.1, 0), (t.2.2.2, 0)))))
      (by
        change _ = Distribution.fTransform (Prod.map (fun t => (t, 0))
          (Prod.map (fun t => (t, 0)) (Prod.map (fun t => (t, 0)) (fun t => (t, 0))))) _
        rw [Distribution.fTransform_prod, Distribution.fTransform_prod,
          Distribution.fTransform_prod])
      (fun t => rand (entries t))]
  · rw [← Resource.sample_fTransform (A := OneCCA bits K q) entries _
      (fun x => Resource.ofFunction (rand x)), Rand.sampled,
      Resource.sample_congr_law (P' := Distribution.fTransform (fun p => ((p.1, p.2.1), p.2.2))
        (Distribution.prod (Distribution.prod keyGen.1 (RSA.residues (bits := bits)).1)
          (Distribution.prod (Distribution.uniform K)
            (Distribution.uniform (RSA.Residue bits → K)))))
        (Distribution.fTransform_assoc_prod _ _ _).symm]
    conv_rhs => rw [Resource.sample_fTransform]
    rw [Resource.sample_congr_law (P' := Distribution.fTransform (fun p => ((p.1, p.2.1), p.2.2))
        (Distribution.prod keyGen.1 (Distribution.prod (RSA.residues (bits := bits)).1
          (Distribution.prod (Distribution.uniform K)
            (Distribution.uniform (RSA.Residue bits → K))))))
        (Distribution.fTransform_assoc_prod _ _ _).symm]
    conv_rhs => rw [Resource.sample_fTransform]
    by_cases hk : 0 < n
    · have law : Distribution.fTransform entries
          (Distribution.prod (Distribution.pi fun _ => (Rand.law1 K keyGen).1)
            (Distribution.prod (Distribution.pi fun _ => (Rand.law2 K keyGen).1)
              (Distribution.prod (Distribution.pi fun _ => (Rand.law3 K keyGen).1)
                (Distribution.pi fun _ => (Rand.law4 K keyGen).1)))) =
          Distribution.prod keyGen.1 (Distribution.prod (RSA.residues (bits := bits)).1
            (Distribution.prod (Distribution.uniform K)
              (Distribution.uniform (RSA.Residue bits → K)))) := by
        rw [Distribution.fTransform_prod, Distribution.fTransform_prod,
          Distribution.fTransform_prod, sourceEntry_zero_law _ hk, sourceEntry_zero_law _ hk,
          sourceEntry_zero_law _ hk, sourceEntry_zero_law _ hk]
        rfl
      exact Resource.sample_congr_law law _
    · exact Resource.eq_of_not_domain fun h hd => hk
        (Nat.mul_pos (by norm_num [Rand.bound]) (bound_pos_of_domain hd))
  · rintro ⟨t₁, t₂, t₃, t₄⟩
    refine automatonSystem_of_stored _ rand ((t₁, 0), ((t₂, 0), ((t₃, 0), (t₄, 0))))
      (entries (t₁, t₂, t₃, t₄))
      (fun i x => ⟨((t₁, 1), ((t₂, 1), ((t₃, 1), (t₄, 1)))), ?_⟩) (fun r i x => ⟨r, ?_⟩)
    · refine Program.combine_eq_of_invoke _ _ (n := 4) ?_
      cases i <;> simp [Program.invoke, Rand.body, callProg, returnProg, parallelStep,
        sourceStep, sourceEntry, rand, sampled, entries, n]
      -- Decapsulation at the challenge ciphertext.
      split_ifs <;> first | rfl | (split <;> rfl)
    · refine Program.combine_eq_of_invoke _ _ (n := 0) ?_
      cases i <;> simp [Program.invoke, Rand.body, returnProg, rand, sampled]
      split <;> rfl

/-- **The uniform `c*` is `R*^e`**: in `kem-1cca-rand+ro`, the challenge ciphertext is the
`e`-th power of a uniform residue. -/
lemma Rand.sampled_eq_power (K : Type) [Fintype K] [Nonempty K] [DecidableEq K]
    (keyGen : Distribution.ProbDist (RSA.Key bits))
    (correct : RSA.Correct keyGen) (q : KEMOneCCA.Port → ℕ) :
    Rand.sampled K keyGen (q := q) =
      Resource.sample (Distribution.prod (Distribution.prod (Distribution.prod keyGen.1
          (RSA.residues (bits := bits)).1) (Distribution.uniform K))
          (Distribution.uniform (RSA.Residue bits → K))) fun x =>
        Resource.ofFunction (A := OneCCA bits K q) fun
          | .pk => fun _ => (x.1.1.1.N, x.1.1.1.e)
          | .enc => fun _ => (x.1.1.1.pow (x.1.1.2 x.1.1.1.N) x.1.1.1.e.val, x.1.2)
          | .dec => fun c =>
            if c = x.1.1.1.pow (x.1.1.2 x.1.1.1.N) x.1.1.1.e.val then some x.1.2
            else decapsulate x.1.1.1 x.2 c
          | .ro => fun A => x.2 A := by
  classical
  -- Raising `R*` to `e` is a bijection of `ℤ_N` by `correct`, so it keeps the uniform residue.
  let power : RSA.Key bits × (RSA.Residue bits → RSA.Residue bits) →
      RSA.Key bits × (RSA.Residue bits → RSA.Residue bits) := fun p =>
    (p.1, Function.update p.2 p.1.N (p.1.pow (p.2 p.1.N) p.1.e.val))
  symm
  unfold Rand.sampled
  refine Resource.sample_eq_sample_of_fTransform _ _ (Prod.map (Prod.map power id) id) _ _ ?_
    fun x => ?_
  · rw [Distribution.fTransform_prod, Distribution.fTransform_prod, Distribution.fTransform_id,
      Distribution.fTransform_id]
    congr 2
    refine Distribution.fTransform_prod_fiber _ _
      (fun (k : RSA.Key bits) (Rs : RSA.Residue bits → RSA.Residue bits) =>
        Function.update Rs k.N (k.pow (Rs k.N) k.e.val)) fun k hk => ?_
    exact Distribution.fTransform_update_pi (fun N => (RSA.residue N).1) k.N _
      (RSA.residue_pow k (correct k hk))
  · congr 1
    funext i
    cases i <;> simp [power]

/-! ## The reduction on sampled functions

On the RSA library of a key, a challenge `Y` and a check, the reduction answers with its sample
`(T, K*)`. On `rsa-real` these answers are those of `kem-1cca-real+ro` at `R* := Y^d` and the
oracle `T[Y ↦ K*] ∘ σ`, where `σ` raises to `e` on `ℤ_N` and is the identity elsewhere; on
`rsa-fake` they are those of `kem-1cca-rand+ro` at `c* := Y` and the oracle `T ∘ σ`. By
correctness `σ` and raising to `d` permute `ℤ_N`, so the re-indexed samples have the laws of the
libraries. -/

/-- The answers of the reduction on the RSA library of `key`, `Y` and `chk`, with its sample
`(T, K*)`. -/
def reductionAnswers (key : RSA.Key bits) (Y : RSA.Residue bits) (chk : RSA.Residue bits → Bool)
    (TK : (RSA.Residue bits → K) × K) :
    ∀ i, KEMOneCCA.Input (RSA.Residue bits) (RSA.Residue bits) i →
      KEMOneCCA.Output (RSA.Residue bits × RSA.Residue bits) (RSA.Residue bits) K K i
  | .pk => fun _ => (key.N, key.e)
  | .enc => fun _ => (Y, TK.2)
  | .dec => fun c =>
    if c = Y then some TK.2 else if c.val < key.N.val then some (TK.1 c) else none
  | .ro => fun A =>
    if A.val < key.N.val then (if chk A then TK.2 else TK.1 (RSA.powMod key.N key.e A)) else TK.1 A

/-- **The reduction on an RSA library**: attached to the RSA library of `key`, `Y` and `chk`, the
reduction answers with its sample `(T, K*)`. -/
lemma 𝓡.smul_ofFunction (q : KEMOneCCA.Port → ℕ) (key : RSA.Key bits) (Y : RSA.Residue bits)
    (chk : RSA.Residue bits → Bool) :
    𝓡.perLabel q • Resource.ofFunction (A := RSAChallenge.perPort bits (insideBudget q))
        (RSA.library key Y chk) =
      Resource.sample (𝓡.law1 bits K).1 fun TK =>
        Resource.ofFunction (A := OneCCA bits K q)
          (reductionAnswers key Y chk TK) := by
  unfold 𝓡.perLabel Converter.ofLabelBoundedProgram 𝓡.randomness
  refine ofDDC_ofProgramOn_source_smul_ofFunction (A := OneCCA bits K q)
    (B := RSAChallenge.perPort bits (insideBudget q)) (Z := lawType (𝓡.law1 bits K))
    (k := 𝓡.bound bits K * ∑ i, q i) none (𝓡.body bits K)
    (𝓡.bound_spec bits K) _ (𝓡.law1 bits K) (RSA.library key Y chk) _
    (fun t c => ?_) fun h hd => Nat.mul_pos (by norm_num [𝓡.bound]) (bound_pos_of_domain hd)
  -- The first invocation reads the sample and stores it; every invocation answers with it.
  refine automatonSystem_of_stored _ (reductionAnswers key Y chk) _ (sourceEntry _ t c)
    (fun i x => ⟨((), (t, c + 1)), ?_⟩) (fun r i x => ⟨r, ?_⟩)
  · refine Program.combine_eq_of_invoke _ _ (n := 3) ?_
    cases i <;> simp [Program.invoke, 𝓡.body, callProg, returnProg, parallelStep, sourceStep,
      sourceEntry, reductionAnswers, RSA.library] <;> split_ifs <;>
      simp [returnProg, callProg, *]
  · refine Program.combine_eq_of_invoke _ _ (n := 2) ?_
    cases i <;> simp [Program.invoke, 𝓡.body, callProg, returnProg, parallelStep,
      reductionAnswers, RSA.library] <;> split_ifs <;>
      simp [returnProg, callProg, *]

/-- **The reduction on a sampled RSA library** samples the key, the challenges and its own
sample `(T, K*)` once. -/
lemma 𝓡.smul_sample (keyGen : Distribution.ProbDist (RSA.Key bits)) (q : KEMOneCCA.Port → ℕ)
    (chk : RSA.Key bits × (RSA.Residue bits → RSA.Residue bits) → RSA.Residue bits → Bool) :
    𝓡.perLabel (K := K) q • Resource.sample
        (Distribution.prod keyGen.1 (RSA.residues (bits := bits)).1)
        (fun kY => Resource.ofFunction (A := RSAChallenge.perPort bits (insideBudget q))
          (RSA.library kY.1 (kY.2 kY.1.N) (chk kY))) =
      Resource.sample (Distribution.prod (Distribution.prod keyGen.1
          (RSA.residues (bits := bits)).1) (𝓡.law1 bits K).1) fun x =>
        Resource.ofFunction (A := OneCCA bits K q)
          (reductionAnswers x.1.1 (x.1.2 x.1.1.N) (chk x.1) x.2) := by
  rw [Resource.smul_sample]
  simp only [𝓡.smul_ofFunction]
  exact Resource.sample_sample _ _ _

/-- The oracle of `kem-1cca-real+ro` from the reduction's sample on `rsa-real`: `T[Y ↦ K*] ∘ σ`. -/
def realOracle (kY : RSA.Key bits × (RSA.Residue bits → RSA.Residue bits))
    (TK : (RSA.Residue bits → K) × K) : RSA.Residue bits → K :=
  fun A => Function.update TK.1 (kY.2 kY.1.N) TK.2 (kY.1.σ A)

/-- The residues `R*` of `kem-1cca-real+ro` from the challenges of `rsa-real`: `R* := Y^d`. -/
def realRandomness (kY : RSA.Key bits × (RSA.Residue bits → RSA.Residue bits)) :
    RSA.Key bits × (RSA.Residue bits → RSA.Residue bits) :=
  (kY.1, Function.update kY.2 kY.1.N (kY.1.pow (kY.2 kY.1.N) kY.1.d.val))

/-- **The samples of `kem-1cca-real+ro` from those of the reduction on `rsa-real`**. -/
def realIndex (x : (RSA.Key bits × (RSA.Residue bits → RSA.Residue bits)) ×
    ((RSA.Residue bits → K) × K)) :
    (RSA.Key bits × (RSA.Residue bits → RSA.Residue bits)) × (RSA.Residue bits → K) :=
  (realRandomness x.1, realOracle x.1 x.2)

/-- **The re-indexed samples have the law of those of `kem-1cca-real+ro`**: by correctness `σ`
and raising to `d` permute `ℤ_N`, and `T[Y ↦ K*]` is a uniform oracle. -/
lemma realIndex_law (keyGen : Distribution.ProbDist (RSA.Key bits))
    (correct : RSA.Correct keyGen) :
    Distribution.fTransform realIndex (Distribution.prod (Distribution.prod keyGen.1
        (RSA.residues (bits := bits)).1) (𝓡.law1 bits K).1) =
      Distribution.prod (Distribution.prod keyGen.1 (RSA.residues (bits := bits)).1)
        (Distribution.uniform (RSA.Residue bits → K)) := by
  classical
  -- The oracle first, fiberwise over the key and the challenges; then `R*`.
  rw [show (realIndex : _ → (RSA.Key bits × (RSA.Residue bits → RSA.Residue bits)) ×
      (RSA.Residue bits → K)) =
      Prod.map realRandomness id ∘ (fun p => (p.1, realOracle p.1 p.2)) from rfl,
    ← Distribution.fTransform_comp,
    Distribution.fTransform_prod_fiber_map _ _
      (Distribution.uniform (RSA.Residue bits → K)) realOracle ?oracle,
    ← Distribution.fTransform_prod_left]
  · congr 1
    exact Distribution.fTransform_prod_fiber _ _ (fun (k : RSA.Key bits)
      (Ys : RSA.Residue bits → RSA.Residue bits) =>
        Function.update Ys k.N (k.pow (Ys k.N) k.d.val)) fun k hk =>
      Distribution.fTransform_update_pi (fun N => (RSA.residue N).1) k.N _
        (RSA.residue_pow_d k (correct k hk))
  · intro kY hkY
    obtain ⟨hk, -⟩ := Finset.mem_product.mp (Distribution.support_prod_subset _ _ hkY)
    let σe := Equiv.ofBijective _ (RSA.σ_bijective kY.1 (correct kY.1 hk))
    rw [show realOracle kY = (σe.symm.arrowCongr (Equiv.refl _)) ∘
        (fun TK : (RSA.Residue bits → K) × K =>
          Function.update TK.1 (kY.2 kY.1.N) TK.2) from rfl, ← Distribution.fTransform_comp]
    change Distribution.fTransform _ (Distribution.fTransform _ (Distribution.uniform _)) = _
    rw [Distribution.fTransform_update_uniform, Distribution.fTransform_equiv_uniform]

/-- **The reduction on `rsa-real` answers like `kem-1cca-real+ro`** at the re-indexed samples: by
correctness `(Y^d)^e = Y` and `σ(c^d) = c` on `ℤ_N`, and `T[Y ↦ K*]` at `σ A` is `K*` exactly when
`A` is an `e`-th root of `Y`. -/
lemma reduction_real_sampled (keyGen : Distribution.ProbDist (RSA.Key bits))
    (correct : RSA.Correct keyGen) (q : KEMOneCCA.Port → ℕ) :
    Resource.sample (Distribution.prod (Distribution.prod keyGen.1
        (RSA.residues (bits := bits)).1) (𝓡.law1 bits K).1) (fun x =>
      Resource.ofFunction (A := OneCCA bits K q)
        (reductionAnswers x.1.1 (x.1.2 x.1.1.N)
          (fun X => decide (x.1.2 x.1.1.N = x.1.1.pow X x.1.1.e.val)) x.2)) =
      Real.sampled K keyGen := by
  refine Resource.sample_eq_sample_of_fTransform_support _ _ realIndex _ _
    (realIndex_law keyGen correct) fun x hx => ?_
  obtain ⟨⟨key, Ys⟩, T, K⟩ := x
  obtain ⟨hkY, -⟩ := Finset.mem_product.mp (Distribution.support_prod_subset _ _ hx)
  obtain ⟨hk, hYs⟩ := Finset.mem_product.mp (Distribution.support_prod_subset _ _ hkY)
  have hkey := correct key hk
  have hY : (Ys key.N).val < key.N.val :=
    RSA.lt_of_mem_support_residue key.2 (Distribution.ProbDist.mem_support_pi hYs key.N)
  have σd : ∀ c : RSA.Residue bits, c.val < key.N.val → key.σ (key.pow c key.d.val) = c :=
    fun c hc => by
      rw [RSA.Key.σ, if_pos (show (key.pow c key.d.val).val < key.N.val from Nat.mod_lt _ key.2),
        RSA.pow_d_pow_e key hkey hc]
  congr 1
  funext i
  cases i
  · rfl
  · funext _
    simp only [reductionAnswers, realIndex, realRandomness, realOracle, encapsulate,
      Function.update_self, RSA.pow_d_pow_e key hkey hY, σd _ hY]
  · funext c
    simp only [reductionAnswers, realIndex, realRandomness, realOracle, decapsulate]
    by_cases hcY : c = Ys key.N
    · subst hcY
      simp [hY, σd _ hY]
    · by_cases hc : c.val < key.N.val
      · simp [hcY, hc, σd _ hc]
      · simp [hcY, hc]
  · funext A
    simp only [reductionAnswers, realIndex, realRandomness, realOracle, RSA.Key.σ,
      RSA.powMod_eq_pow]
    by_cases hA : A.val < key.N.val
    · by_cases he : Ys key.N = key.pow A key.e.val
      · simp [hA, he]
      · simp [hA, he, Function.update_of_ne (Ne.symm he)]
    · have hne : A ≠ Ys key.N := fun h => hA (h ▸ hY)
      simp [hA, Function.update_of_ne hne]

/-- The key `K*` and the oracle of `kem-1cca-rand+ro` from the reduction's sample on `rsa-fake`:
`K*` and `T ∘ σ`. -/
def fakeSample (kY : RSA.Key bits × (RSA.Residue bits → RSA.Residue bits))
    (TK : (RSA.Residue bits → K) × K) :
    K × (RSA.Residue bits → K) :=
  (TK.2, fun A => TK.1 (kY.1.σ A))

/-- **The samples of `kem-1cca-rand+ro` from those of the reduction on `rsa-fake`**: `c* := Y`. -/
def fakeIndex (x : (RSA.Key bits × (RSA.Residue bits → RSA.Residue bits)) ×
    ((RSA.Residue bits → K) × K)) :
    ((RSA.Key bits × (RSA.Residue bits → RSA.Residue bits)) × K) ×
      (RSA.Residue bits → K) :=
  ((x.1, (fakeSample x.1 x.2).1), (fakeSample x.1 x.2).2)

/-- **The re-indexed samples have the law of those of `kem-1cca-rand+ro`**: by correctness `σ`
permutes the residues. -/
lemma fakeIndex_law (keyGen : Distribution.ProbDist (RSA.Key bits))
    (correct : RSA.Correct keyGen) :
    Distribution.fTransform fakeIndex (Distribution.prod (Distribution.prod keyGen.1
        (RSA.residues (bits := bits)).1) (𝓡.law1 bits K).1) =
      Distribution.prod (Distribution.prod (Distribution.prod keyGen.1
        (RSA.residues (bits := bits)).1) (Distribution.uniform K))
        (Distribution.uniform (RSA.Residue bits → K)) := by
  classical
  rw [show (fakeIndex : _ → ((RSA.Key bits × (RSA.Residue bits → RSA.Residue bits)) ×
      K) × (RSA.Residue bits → K)) =
      (fun p => ((p.1, p.2.1), p.2.2)) ∘ (fun p => (p.1, fakeSample p.1 p.2)) from rfl,
    ← Distribution.fTransform_comp,
    Distribution.fTransform_prod_fiber_map _ _ (Distribution.prod
      (Distribution.uniform K) (Distribution.uniform (RSA.Residue bits → K)))
      fakeSample ?fiber, Distribution.fTransform_assoc_prod]
  intro kY hkY
  obtain ⟨hk, -⟩ := Finset.mem_product.mp (Distribution.support_prod_subset _ _ hkY)
  let σe := Equiv.ofBijective _ (RSA.σ_bijective kY.1 (correct kY.1 hk))
  change Distribution.fTransform _ (Distribution.uniform _) = _
  rw [← Distribution.prod_uniform, show fakeSample kY = Prod.swap ∘
      Prod.map (σe.symm.arrowCongr (Equiv.refl K)) id from rfl,
    ← Distribution.fTransform_comp, Distribution.fTransform_prod,
    Distribution.fTransform_equiv_uniform, Distribution.fTransform_id,
    Distribution.fTransform_swap_prod]

/-- **The reduction on `rsa-fake` answers like `kem-1cca-rand+ro`** at the re-indexed samples: by
correctness `σ(c^d) = c` on `ℤ_N`. -/
lemma reduction_fake_sampled (keyGen : Distribution.ProbDist (RSA.Key bits))
    (correct : RSA.Correct keyGen) (q : KEMOneCCA.Port → ℕ) :
    Resource.sample (Distribution.prod (Distribution.prod keyGen.1
        (RSA.residues (bits := bits)).1) (𝓡.law1 bits K).1) (fun x =>
      Resource.ofFunction (A := OneCCA bits K q)
        (reductionAnswers x.1.1 (x.1.2 x.1.1.N) (fun _ => false) x.2)) =
      Rand.sampled K keyGen := by
  refine Resource.sample_eq_sample_of_fTransform_support _ _ fakeIndex _ _
    (fakeIndex_law keyGen correct) fun x hx => ?_
  obtain ⟨⟨key, Ys⟩, T, K⟩ := x
  obtain ⟨hkY, -⟩ := Finset.mem_product.mp (Distribution.support_prod_subset _ _ hx)
  obtain ⟨hk, -⟩ := Finset.mem_product.mp (Distribution.support_prod_subset _ _ hkY)
  have hkey := correct key hk
  have σd : ∀ c : RSA.Residue bits, c.val < key.N.val → key.σ (key.pow c key.d.val) = c :=
    fun c hc => by
      rw [RSA.Key.σ, if_pos (show (key.pow c key.d.val).val < key.N.val from Nat.mod_lt _ key.2),
        RSA.pow_d_pow_e key hkey hc]
  congr 1
  funext i
  cases i
  · rfl
  · rfl
  · funext c
    simp only [reductionAnswers, fakeIndex, fakeSample, decapsulate]
    by_cases hcY : c = Ys key.N
    · simp [hcY]
    · by_cases hc : c.val < key.N.val
      · simp [hcY, hc, σd _ hc]
      · simp [hcY, hc]
  · funext A
    simp only [reductionAnswers, fakeIndex, fakeSample, RSA.Key.σ, RSA.powMod_eq_pow]
    by_cases hA : A.val < key.N.val <;> simp [hA]

/-- **The reduction on `rsa-real` is `kem-1cca-real+ro`**. -/
lemma 𝓡_smul_real (keyGen : Distribution.ProbDist (RSA.Key bits)) (correct : RSA.Correct keyGen)
    (q : KEMOneCCA.Port → ℕ) :
    𝓡.perLabel (K := K) q • RSA.Real.perPort keyGen =
      Real.perPort K keyGen (budget := q) := by
  rw [RSA.Real.perPort_eq_sampled, RSA.Real.sampled_eq_library, 𝓡.smul_sample,
    reduction_real_sampled keyGen correct q, Real.perPort_eq_sampled]

/-- **The reduction on `rsa-fake` is `kem-1cca-rand+ro`**. -/
lemma 𝓡_smul_fake (keyGen : Distribution.ProbDist (RSA.Key bits)) (correct : RSA.Correct keyGen)
    (q : KEMOneCCA.Port → ℕ) :
    𝓡.perLabel (K := K) q • (RSA.Reject.perPort bits • RSA.Real.perPort keyGen) =
      Rand.perPort K keyGen (budget := q) := by
  rw [← RSA.Fake.perPort_eq_reject, RSA.Fake.perPort_eq_sampled, RSA.Fake.sampled_eq_library,
    𝓡.smul_sample, reduction_fake_sampled keyGen correct q, Rand.perPort_eq_sampled]

/-! ## The libraries as converters on the real system of RSA-KEM

The notes' `kem-1cca-real+ro` and the converter `kem-1cca-real+ro` on the real system of RSA-KEM
are sampled functions of the oracle, the key and the challenge `(c*, K*)`, which only the
encapsulation under the public key determines, so they have the same law; likewise
`kem-1cca-rand+ro`, whose `c*` is uniform in `ℤ_N` on both sides. -/

/-- **`kem-1cca-real+ro` is the converter `kem-1cca-real+ro` on the real system of RSA-KEM.** -/
lemma Real.perPort_eq_oneCCAReal (keyGen : Distribution.ProbDist (RSA.Key bits))
    (q : KEMOneCCA.Port → ℕ) :
    Real.perPort K keyGen (budget := q) =
      KEM.OneCCAReal.perLabel q •
        KEM.RealRO (scheme K keyGen) (KEM.OneCCA.insideBudget q) (q .ro) := by
  -- The notes' answers are those of the converter at the keys and the encapsulation of `R*`.
  let keysOf : RSA.Key bits → (RSA.Residue bits × RSA.Residue bits) ×
      (RSA.Residue bits × RSA.Residue bits) := fun key => ((key.N, key.e), (key.N, key.d))
  rw [KEM.OneCCAReal.smul_realRO, Real.perPort_eq_sampled, Real.sampled]
  refine (Eq.trans (congrArg _ (funext fun x => ?answers)) (Resource.sample_sample
    (Distribution.prod keyGen.1 (RSA.residues (bits := bits)).1)
    (Distribution.uniform (RSA.Residue bits → K)) fun kR RO =>
      Resource.ofFunction (A := OneCCA bits K q) (KEM.OneCCAReal.answers (scheme K keyGen) RO
        (keysOf kR.1) (encapsulate kR.1 RO (kR.2 kR.1.N)))).symm).trans ?_
  · congr 1
    funext i
    cases i
    · rfl
    · rfl
    · funext c
      simp only [KEM.OneCCAReal.answers, scheme, decapsulate, keysOf, RSA.powMod_eq_pow]
    · rfl
  rw [Resource.sample_comm]
  congr 1
  funext RO
  -- Both sample the keys and the challenge `(R*^e, RO(R*))` for a uniform `R* ∈ ℤ_N`.
  let F : ((RSA.Residue bits × RSA.Residue bits) × (RSA.Residue bits × RSA.Residue bits)) ×
      (RSA.Residue bits × K) → Resource (OneCCA bits K q) := fun y =>
    Resource.ofFunction (KEM.OneCCAReal.answers (scheme K keyGen) RO y.1 y.2)
  let ψ₁ : RSA.Key bits × (RSA.Residue bits → RSA.Residue bits) →
      ((RSA.Residue bits × RSA.Residue bits) × (RSA.Residue bits × RSA.Residue bits)) ×
        (RSA.Residue bits × K) := fun kR => (keysOf kR.1, encapsulate kR.1 RO (kR.2 kR.1.N))
  let ψ₂ : ((RSA.Residue bits × RSA.Residue bits) × (RSA.Residue bits × RSA.Residue bits)) ×
      (RSA.Residue bits × RSA.Residue bits → RSA.Residue bits × K) →
      ((RSA.Residue bits × RSA.Residue bits) × (RSA.Residue bits × RSA.Residue bits)) ×
        (RSA.Residue bits × K) := fun x => (x.1, x.2 x.1.1)
  refine (Resource.sample_eq_sample_of_fTransform _ _ ψ₁ _ F rfl fun _ => rfl).trans
    ((Resource.sample_congr_law ?_ F).trans
      (Resource.sample_eq_sample_of_fTransform _ _ ψ₂ _ F rfl fun _ => rfl).symm)
  rw [show (scheme K keyGen RO).gen.1 = Distribution.fTransform keysOf keyGen.1 from rfl,
    Distribution.fTransform_prod_left, Distribution.fTransform_comp,
    show ψ₁ = Prod.map keysOf id ∘ fun kR => (kR.1, encapsulate kR.1 RO (kR.2 kR.1.N)) from rfl,
    show ψ₂ ∘ Prod.map keysOf id = Prod.map keysOf id ∘ fun x => (x.1, x.2 (x.1.N, x.1.e)) from rfl,
    ← Distribution.fTransform_comp, ← Distribution.fTransform_comp]
  congr 1
  refine Distribution.fTransform_prod_fiber_congr keyGen.1 (RSA.residues (bits := bits)).1
    (scheme K keyGen RO).encapsulations.1 (fun key Rs => encapsulate key RO (Rs key.N))
    (fun key encs => encs (key.N, key.e)) fun key _ => ?_
  -- The encapsulation under `(N, e)` is that of a uniform `R* ∈ ℤ_N`.
  rw [show (fun Rs : RSA.Residue bits → RSA.Residue bits => encapsulate key RO (Rs key.N)) =
      encapsulate key RO ∘ fun Rs => Rs key.N from rfl, ← Distribution.fTransform_comp,
    RSA.fTransform_eval_residues]
  change _ = Distribution.fTransform (fun f => f (key.N, key.e))
    (Distribution.ProbDist.pi fun pk => (scheme K keyGen RO).encaps pk).1
  rw [Distribution.ProbDist.fTransform_eval_pi]
  change _ = Distribution.fTransform _ (RSA.residue key.N).1
  congr 1
  funext R
  simp only [encapsulate, RSA.powMod_eq_pow]

/-- **`kem-1cca-rand+ro` is the converter `kem-1cca-rand+ro` on the real system of RSA-KEM**,
with the random ciphertexts uniform in `ℤ_N`. -/
lemma Rand.perPort_eq_oneCCARand (keyGen : Distribution.ProbDist (RSA.Key bits))
    (q : KEMOneCCA.Port → ℕ) :
    Rand.perPort K keyGen (budget := q) =
      KEM.OneCCARand.perLabel ciphertexts q •
        KEM.RealRO (scheme K keyGen) (KEM.OneCCA.insideBudget q) (q .ro) := by
  -- The notes' answers are those of the converter at the keys and the challenge `(c*, K*)`.
  let keysOf : RSA.Key bits → (RSA.Residue bits × RSA.Residue bits) ×
      (RSA.Residue bits × RSA.Residue bits) := fun key => ((key.N, key.e), (key.N, key.d))
  rw [KEM.OneCCARand.smul_realRO, Rand.perPort_eq_sampled, Rand.sampled]
  refine (Eq.trans (congrArg _ (funext fun x => ?answers)) (Resource.sample_sample
    (Distribution.prod (Distribution.prod keyGen.1 (RSA.residues (bits := bits)).1)
      (Distribution.uniform K))
    (Distribution.uniform (RSA.Residue bits → K)) fun kc RO =>
      Resource.ofFunction (A := OneCCA bits K q) (KEM.OneCCARand.answers (scheme K keyGen) RO
        (keysOf kc.1.1) (kc.1.2 kc.1.1.N) kc.2)).symm).trans ?_
  · congr 1
    funext i
    cases i
    · rfl
    · rfl
    · funext c
      simp only [KEM.OneCCARand.answers, scheme, decapsulate, keysOf, RSA.powMod_eq_pow]
    · rfl
  rw [Resource.sample_comm]
  congr 1
  funext RO
  -- Both sample the keys, a uniform `c* ∈ ℤ_N` and a uniform `K*`.
  let F : (((RSA.Residue bits × RSA.Residue bits) × (RSA.Residue bits × RSA.Residue bits)) ×
      RSA.Residue bits) × K → Resource (OneCCA bits K q) := fun y =>
    Resource.ofFunction (KEM.OneCCARand.answers (scheme K keyGen) RO y.1.1 y.1.2 y.2)
  let φ₁ : RSA.Key bits × (RSA.Residue bits → RSA.Residue bits) →
      ((RSA.Residue bits × RSA.Residue bits) × (RSA.Residue bits × RSA.Residue bits)) ×
        RSA.Residue bits := fun kR => (keysOf kR.1, kR.2 kR.1.N)
  let φ₂ : ((RSA.Residue bits × RSA.Residue bits) × (RSA.Residue bits × RSA.Residue bits)) ×
      (RSA.Residue bits × RSA.Residue bits → RSA.Residue bits) →
      ((RSA.Residue bits × RSA.Residue bits) × (RSA.Residue bits × RSA.Residue bits)) ×
        RSA.Residue bits := fun x => (x.1, x.2 x.1.1)
  refine (Resource.sample_eq_sample_of_fTransform _ _ (Prod.map φ₁ id) _ F rfl
    fun _ => rfl).trans ((Resource.sample_congr_law ?_ F).trans
      (Resource.sample_eq_sample_of_fTransform _ _ (Prod.map φ₂ id) _ F rfl fun _ => rfl).symm)
  rw [Distribution.fTransform_prod, Distribution.fTransform_prod]
  congr 1
  rw [show (scheme K keyGen RO).gen.1 = Distribution.fTransform keysOf keyGen.1 from rfl,
    Distribution.fTransform_prod_left, Distribution.fTransform_comp,
    show φ₁ = Prod.map keysOf id ∘ fun kR => (kR.1, kR.2 kR.1.N) from rfl,
    show φ₂ ∘ Prod.map keysOf id = Prod.map keysOf id ∘ fun x => (x.1, x.2 (x.1.N, x.1.e)) from rfl,
    ← Distribution.fTransform_comp, ← Distribution.fTransform_comp]
  congr 1
  refine Distribution.fTransform_prod_fiber_congr keyGen.1 (RSA.residues (bits := bits)).1
    (Distribution.ProbDist.pi ciphertexts).1 (fun key Rs => Rs key.N)
    (fun key cs => cs (key.N, key.e)) fun key _ => ?_
  -- The random ciphertext under `(N, e)` is uniform in `ℤ_N`.
  rw [RSA.fTransform_eval_residues, Distribution.ProbDist.fTransform_eval_pi]
  rfl

/-- **RSA-KEM** [1, §7]: if the RSA assumption holds within `ε`, then RSA-KEM is
single-challenge IND$-CCA-secure in the random-oracle model, with the random ciphertexts uniform
in `ℤ_N`, within `ε` at the distinguishers with the reduction `𝓡` absorbed, which calls
`rsa.challenge()` once per query and `rsa.check` once per oracle query. -/
theorem rsa_kem_cca [AdmissibleDistinguishers] (keyGen : Distribution.ProbDist (RSA.Key bits))
    (correct : RSA.Correct keyGen) (q : KEMOneCCA.Port → ℕ) :
    ∀ ε, RSA.Assumption keyGen ε →
      KEM.OneCCA (scheme K keyGen) ciphertexts (q := q) fun D => ε (absorb (𝓡.perLabel q) D) := by
  intro ε secure
  show KEM.OneCCAReal.perLabel q • KEM.RealRO (scheme K keyGen) (KEM.OneCCA.insideBudget q) (q .ro)
    ≃[_] KEM.OneCCARand.perLabel ciphertexts q •
      KEM.RealRO (scheme K keyGen) (KEM.OneCCA.insideBudget q) (q .ro)
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    KEM.OneCCAReal.perLabel q • KEM.RealRO (scheme K keyGen) (KEM.OneCCA.insideBudget q) (q .ro) =
        Real.perPort K keyGen := (Real.perPort_eq_oneCCAReal keyGen q).symm
    _ = 𝓡.perLabel q • RSA.Real.perPort keyGen := (𝓡_smul_real keyGen correct q).symm
    _ ≃[ε ∘ absorb (𝓡.perLabel q)] 𝓡.perLabel q • (RSA.Reject.perPort bits •
        RSA.Real.perPort keyGen) := AdmissibleDistinguishers.substitutesWithin_context _ secure
    _ = Rand.perPort K keyGen := 𝓡_smul_fake keyGen correct q
    _ = KEM.OneCCARand.perLabel ciphertexts q •
        KEM.RealRO (scheme K keyGen) (KEM.OneCCA.insideBudget q) (q .ro) :=
      Rand.perPort_eq_oneCCARand keyGen q

/-- **RSA-KEM** [1, §7], on sampled functions: the statement of `rsa_kem_cca` with the notes'
four libraries as their sampled functions. -/
theorem rsa_kem_cca_sampled [AdmissibleDistinguishers]
    (K : Type) [Fintype K] [Nonempty K] [DecidableEq K]
    (keyGen : Distribution.ProbDist (RSA.Key bits)) (correct : RSA.Correct keyGen)
    (q : KEMOneCCA.Port → ℕ) :
    ∀ ε, RSA.Real.sampled keyGen ≃[ε] RSA.Fake.sampled keyGen →
      Real.sampled K keyGen ≃[fun D => ε (absorb (𝓡.perLabel (K := K) q) D)]
        Rand.sampled K keyGen := by
  intro ε secure
  have chain := rsa_kem_cca (K := K) keyGen correct q ε (RSA.Assumption.of_sampled keyGen secure)
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    Real.sampled K keyGen = Real.perPort K keyGen :=
      (Real.perPort_eq_sampled K keyGen q).symm
    _ = KEM.OneCCAReal.perLabel q •
        KEM.RealRO (scheme K keyGen) (KEM.OneCCA.insideBudget q) (q .ro) :=
      Real.perPort_eq_oneCCAReal keyGen q
    _ ≃[fun D => ε (absorb (𝓡.perLabel q) D)] KEM.OneCCARand.perLabel ciphertexts q •
        KEM.RealRO (scheme K keyGen) (KEM.OneCCA.insideBudget q) (q .ro) := chain
    _ = Rand.perPort K keyGen := (Rand.perPort_eq_oneCCARand keyGen q).symm
    _ = Rand.sampled K keyGen := Rand.perPort_eq_sampled K keyGen q

end

end ProofLadders.RSAKEM
