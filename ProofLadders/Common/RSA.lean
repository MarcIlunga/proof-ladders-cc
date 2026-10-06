import ConstructiveCryptography.DSL
import ConstructiveCryptography.Notation
import ConstructiveCryptography.Tactics.Substitution
import ProofLadders.Common.Probability
import ProofLadders.Common.Functional
import Mathlib.Data.Nat.Totient

/-!
# The RSA assumption, as libraries

The RSA libraries of the ladder [1, §7–8], in the form of the library's Commons notions: a notion
is the pair of its systems, a converter applied to the real library, and the predicate of the same
name states it for the admitted distinguishers, `X₀ ≃[ε] X₁`.

`RSA.KeyGen` is a law on keys `(N, e, d)` whose entries are below `2^bits`; a residue modulo `N`
is a number below `N`, in `Fin (2^bits)`, and `ℤ_N` is the uniform law on them. Interface
alphabets are fixed finite types, so the residues of every modulus share the type
`RSA.Residue bits`.

* `rsa-real` and `rsa-fake` [1, §7]: the public key and a uniform challenge `Y ∈ ℤ_N`; `rsa-real`
  checks whether `X` is an `e`-th root of `Y`, and `rsa-fake` is the converter `Reject` on it,
  which rejects every `X`.
* `rsa*-real` and `rsa*-fake` [1, §8]: the public key and fresh challenges; `rsa*-real` checks
  whether `X` is an `e`-th root of one of them, and `rsa*-fake` is the converter `Reject*` on it.

The units modulo `N` and their uniform law serve the random self-reduction: `Y · r^e` is a
permutation of the units for a unit `Y` and a correct key, and a uniform residue is a uniform unit
with probability `φ(N)/N`.

Upstream candidates: the whole module, for a new module `Commons.Definitions.RSA`.

## Main definitions

* `RSA.Key bits`, `RSA.Residue bits`, `RSA.Key.pow`: keys, residues, and `x^n mod N`
* `RSA.residue N`, `RSA.residues`: the uniform law on `ℤ_N`, and its samples for every modulus
* `RSA.Correct keyGen`: `(x^e)^d ≡ x (mod N)` for every generated key
* `RSA.Key.σ`: raising to `e` on `ℤ_N`, and the identity on the other residues
* `RSA.NonUnitBound keyGen δ`: a uniform residue is a non-unit with probability at most `δ`
* `RSAChallenge bits`, `RSA.Real`, `RSA.Reject`, `RSA.Assumption`: the RSA assumption, and
  `RSA.Fake`, the notes' `rsa-fake`
* `RSAStar bits`, `RSAStar.Real`, `RSAStar.Reject`, `RSAStar.Assumption`: its many-challenge form,
  and `RSAStar.Fake`, the notes' `rsa*-fake`
* `RSA.Real.sampled`, `RSA.Fake.sampled`: the RSA libraries as sampled functions
* `RSA.powMod`, `RSA.library`: `A^e mod N` from residues, and the RSA library as a function
* `RSAIndexed bits n`, `RSAStar.Indexed.real`, `RSAStar.Indexed.Reject`, `RSAStar.Indexed`: the
  many-challenge form with indexed challenges, as sampled functions, and `RSAStar.Indexed.fake`
* `RSAStar.Count`: the indexed challenges given out by their number
* `RSA.mulMod`, `RSA.invMod`, `RSA.IsUnit`: products, inverses and units modulo `N`
* `RSA.unit N`, `RSA.unitTables n`: the uniform law on the units modulo `N`, and its samples for
  every modulus and each of `n` indices

## Main results

* `RSA.residue_map`, `RSA.residue_pow`, `RSA.residue_pow_d`: a permutation of `ℤ_N`, raising to
  `e` and raising to `d` for a correct key, keeps it uniform
* `RSA.pow_d_pow_e`: `(x^d)^e ≡ x (mod N)` for a correct key
* `RSA.σ_bijective`: `σ` is a permutation of the residues for a correct key
* `RSA.Fake.perPort_eq_reject`, `RSAStar.Fake.perPort_eq_reject`,
  `RSAStar.Indexed.fake_eq_reject`: the fake libraries are the rejecting converters on the real
  ones
* `RSA.Reject.smul_ofFunction`, `RSAStar.Indexed.Reject.smul_ofFunction`,
  `RSAStar.Reject.smul_count`: the rejecting converters on functions, and `Reject*` after `Count`
* `RSA.Assumption.of_sampled`: the RSA assumption from its sampled functions
* `RSA.Real.perPort_eq_sampled`, `RSA.Fake.perPort_eq_sampled`: the RSA libraries are sampled
  functions
* `RSA.Real.sampled_eq_library`, `RSA.Fake.sampled_eq_library`: the sampled functions as RSA
  libraries
* `RSAStar.Real.perPort_eq_count`, `RSAStar.Fake.perPort_eq_count`: the many-challenge libraries
  are the indexed ones, counted
* `RSA.unit_mul_pow`: `Y · r^e` keeps the uniform units, for a unit `Y` and a correct key
* `RSA.pow_mulMod_invMod`: a root of `Y · r^e` times `r⁻¹` is a root of `Y`
* `RSA.unit_le_residue`, `RSA.units_le_residues`: uniform residues are uniform units with
  probability `(φ(N)/N)^n`
* `RSA.fTransform_eval_residues`, `RSA.fTransform_eval_unitTables`: the samples at one modulus

## References

1. The symmetric proof ladder, *Security proofs in the style of The Joy of Cryptography*,
   `proof-ladders/symmetric-ladder`, `Notes/selfcontained.tex`.
-/

namespace Commons

open SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface Probability
open scoped SystemAlgebra SystemAlgebra.DSL

/-- Residues modulo every modulus below `2^bits`. -/
abbrev RSA.Residue (bits : ℕ) := Fin (2 ^ bits)

/-- **An RSA key** `(N, e, d)`, with entries below `2^bits` and `N > 0`. -/
abbrev RSA.Key (bits : ℕ) :=
  {key : RSA.Residue bits × RSA.Residue bits × RSA.Residue bits // 0 < key.1.val}

variable {bits : ℕ}

/-- The modulus `N`. -/
def RSA.Key.N (key : RSA.Key bits) : RSA.Residue bits := key.1.1

/-- The public exponent `e`. -/
def RSA.Key.e (key : RSA.Key bits) : RSA.Residue bits := key.1.2.1

/-- The secret exponent `d`. -/
def RSA.Key.d (key : RSA.Key bits) : RSA.Residue bits := key.1.2.2

/-- `x^n mod N`. -/
def RSA.Key.pow (key : RSA.Key bits) (x : RSA.Residue bits) (n : ℕ) : RSA.Residue bits :=
  ⟨x.val ^ n % key.N.val, (Nat.mod_lt _ key.2).trans key.N.isLt⟩

noncomputable section

/-- **The uniform law on `ℤ_N`**: a uniform number below `N`, and `0` for `N = 0`. -/
def RSA.residue (N : RSA.Residue bits) : Distribution.ProbDist (RSA.Residue bits) :=
  haveI : Nonempty {y : RSA.Residue bits // y.val < max N.val 1} :=
    ⟨⟨⟨0, Nat.two_pow_pos bits⟩, lt_max_of_lt_right Nat.one_pos⟩⟩
  Distribution.ProbDist.map Subtype.val
    ⟨Distribution.uniform {y : RSA.Residue bits // y.val < max N.val 1},
      Distribution.uniform_isProbDist⟩

/-- Independent uniform residues modulo every modulus. -/
def RSA.residues : Distribution.ProbDist (RSA.Residue bits → RSA.Residue bits) :=
  Distribution.ProbDist.pi RSA.residue

/-- **Correctness** of a key generation: for every generated key and every residue `x`,
`(x^e)^d ≡ x (mod N)`. -/
def RSA.Correct (keyGen : Distribution.ProbDist (RSA.Key bits)) : Prop :=
  ∀ key ∈ keyGen.1.support, ∀ x : RSA.Residue bits, x.val < key.N.val →
    key.pow (key.pow x key.e.val) key.d.val = x

/-- **A permutation of `ℤ_N` keeps it uniform**: a map of `ℤ_N` into itself, injective there,
keeps the uniform residue. -/
lemma RSA.residue_map (key : RSA.Key bits) (f : RSA.Residue bits → RSA.Residue bits)
    (hf : ∀ y : RSA.Residue bits, y.val < key.N.val → (f y).val < key.N.val)
    (hinj : ∀ y y' : RSA.Residue bits, y.val < key.N.val → y'.val < key.N.val → f y = f y' →
      y = y') :
    Distribution.fTransform f (RSA.residue key.N).1 = (RSA.residue key.N).1 := by
  classical
  have : Nonempty {y : RSA.Residue bits // y.val < max key.N.val 1} :=
    ⟨⟨⟨0, Nat.two_pow_pos bits⟩, lt_max_of_lt_right Nat.one_pos⟩⟩
  have hN : max key.N.val 1 = key.N.val := max_eq_left key.2
  let f' : {y : RSA.Residue bits // y.val < max key.N.val 1} →
      {y : RSA.Residue bits // y.val < max key.N.val 1} := fun y =>
    ⟨f y.1, lt_of_lt_of_eq (hf y.1 (lt_of_lt_of_eq y.2 hN)) hN.symm⟩
  have hinj' : Function.Injective f' := fun y y' h =>
    Subtype.ext (hinj y.1 y'.1 (lt_of_lt_of_eq y.2 hN) (lt_of_lt_of_eq y'.2 hN)
      (congrArg Subtype.val h))
  let e := Equiv.ofBijective f' (Finite.injective_iff_bijective.mp hinj')
  change Distribution.fTransform _ (Distribution.fTransform Subtype.val _) =
    Distribution.fTransform Subtype.val _
  rw [Distribution.fTransform_comp]
  rw [show (f ∘ Subtype.val) = Subtype.val ∘ e from rfl,
    ← Distribution.fTransform_comp, Distribution.fTransform_equiv_uniform e]

/-- **Raising to `e` keeps `ℤ_N` uniform** for a key with `(x^e)^d ≡ x (mod N)`. -/
lemma RSA.residue_pow (key : RSA.Key bits)
    (hkey : ∀ x : RSA.Residue bits, x.val < key.N.val →
      key.pow (key.pow x key.e.val) key.d.val = x) :
    Distribution.fTransform (fun y => key.pow y key.e.val) (RSA.residue key.N).1 =
      (RSA.residue key.N).1 :=
  -- `x ↦ x^e mod N` is injective on `ℤ_N`, `x ↦ x^d mod N` undoing it.
  RSA.residue_map key _ (fun _ _ => Nat.mod_lt _ key.2) fun y y' hy hy' h => by
    rw [← hkey y hy, ← hkey y' hy', h]

/-- **Raising to `d` undoes raising to `e` on `ℤ_N` both ways**: for a key with
`(x^e)^d ≡ x (mod N)`, also `(x^d)^e ≡ x (mod N)`, as `x ↦ x^e` is injective on `ℤ_N`, hence
onto it. -/
lemma RSA.pow_d_pow_e (key : RSA.Key bits)
    (hkey : ∀ x : RSA.Residue bits, x.val < key.N.val →
      key.pow (key.pow x key.e.val) key.d.val = x)
    {x : RSA.Residue bits} (hx : x.val < key.N.val) :
    key.pow (key.pow x key.d.val) key.e.val = x := by
  let f : {y : RSA.Residue bits // y.val < key.N.val} →
      {y : RSA.Residue bits // y.val < key.N.val} :=
    fun y => ⟨key.pow y.1 key.e.val, Nat.mod_lt _ key.2⟩
  have hinj : Function.Injective f := fun y y' h => Subtype.ext (by
    rw [← hkey y.1 y.2, ← hkey y'.1 y'.2]
    exact congrArg (fun z : {y : RSA.Residue bits // y.val < key.N.val} => key.pow z.1 key.d.val) h)
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨x, hx⟩
  have hyx : key.pow y.1 key.e.val = x := congrArg Subtype.val hy
  rw [← hyx, hkey y.1 y.2]

/-- **Raising to `d` keeps `ℤ_N` uniform** for a key with `(x^e)^d ≡ x (mod N)`. -/
lemma RSA.residue_pow_d (key : RSA.Key bits)
    (hkey : ∀ x : RSA.Residue bits, x.val < key.N.val →
      key.pow (key.pow x key.e.val) key.d.val = x) :
    Distribution.fTransform (fun y => key.pow y key.d.val) (RSA.residue key.N).1 =
      (RSA.residue key.N).1 :=
  RSA.residue_map key _ (fun _ _ => Nat.mod_lt _ key.2) fun y y' hy hy' h => by
    rw [← RSA.pow_d_pow_e key hkey hy, ← RSA.pow_d_pow_e key hkey hy', h]

/-- A possible residue modulo `N > 0` is below `N`. -/
lemma RSA.lt_of_mem_support_residue {N y : RSA.Residue bits} (hN : 0 < N.val)
    (hy : y ∈ (RSA.residue N).1.support) : y.val < N.val := by
  obtain ⟨z, -, rfl⟩ := Distribution.ProbDist.mem_support_map hy
  exact lt_of_lt_of_eq z.2 (max_eq_left hN)

/-- **The permutation `σ` of the residues**: `x ↦ x^e mod N` on `ℤ_N`, and the identity on the
other residues. -/
def RSA.Key.σ (key : RSA.Key bits) (x : RSA.Residue bits) : RSA.Residue bits :=
  if x.val < key.N.val then key.pow x key.e.val else x

/-- `σ` is a permutation of the residues for a key with `(x^e)^d ≡ x (mod N)`. -/
lemma RSA.σ_bijective (key : RSA.Key bits)
    (hkey : ∀ x : RSA.Residue bits, x.val < key.N.val →
      key.pow (key.pow x key.e.val) key.d.val = x) :
    Function.Bijective key.σ := by
  refine Finite.injective_iff_bijective.mp fun x y h => ?_
  have hp : ∀ z : RSA.Residue bits, (key.pow z key.e.val).val < key.N.val :=
    fun _ => Nat.mod_lt _ key.2
  unfold RSA.Key.σ at h
  split_ifs at h with hx hy hy
  · rw [← hkey x hx, ← hkey y hy, h]
  · exact absurd (h ▸ hp x) hy
  · exact absurd (h.symm ▸ hp y) hx
  · exact h

/-- **The non-unit probability** of a key generation is at most `δ`: for every generated key, a
uniform residue modulo `N` shares a factor with `N` with probability at most `δ`. -/
def RSA.NonUnitBound (keyGen : Distribution.ProbDist (RSA.Key bits)) (δ : ℝ) : Prop :=
  ∀ key ∈ keyGen.1.support,
    ((key.N.val : ℝ) - Nat.totient key.N.val) / key.N.val ≤ δ

end

interface RSAChallenge(bits : ℕ)
  challenge() → RSA.Residue bits × RSA.Residue bits × RSA.Residue bits
  check(X : RSA.Residue bits) → Bool

interface RSAStar(bits : ℕ)
  pk() → RSA.Residue bits × RSA.Residue bits
  challenge() → RSA.Residue bits
  check(X : RSA.Residue bits) → Bool

noncomputable section

/-! ## The RSA assumption -/

-- `rsa-real`: `(N, e, d) := RSA.KeyGen()`, `Y ← ℤ_N`; `challenge()` returns `(N, e, Y)` and
-- `check(X)` returns `Y ≡_N X^e`.
system RSA.Real(keyGen : Distribution.ProbDist (RSA.Key bits)) : RSAChallenge bits
  initialize
    key ←$ keyGen
    Ys ←$ RSA.residues (bits := bits)
  on challenge() → RSA.Residue bits × RSA.Residue bits × RSA.Residue bits
    return (key.N, key.e, Ys key.N)
  on check(X : RSA.Residue bits) → Bool
    return decide (Ys key.N = key.pow X key.e.val)

-- `rsa-fake`: as `rsa-real`, but `check(X)` returns `false`.
system RSA.Fake(keyGen : Distribution.ProbDist (RSA.Key bits)) : RSAChallenge bits
  initialize
    key ←$ keyGen
    Ys ←$ RSA.residues (bits := bits)
  on challenge() → RSA.Residue bits × RSA.Residue bits × RSA.Residue bits
    return (key.N, key.e, Ys key.N)
  on check(_X : RSA.Residue bits) → Bool
    return false

-- `Reject`: forward `challenge()`, and answer every `check(X)` with `false`.
converter RSA.Reject(bits : ℕ) : RSAChallenge bits
  inside rsa : RSAChallenge bits
  on challenge() → RSA.Residue bits × RSA.Residue bits × RSA.Residue bits
    (N, e, Y) ← rsa.challenge()
    return (N, e, Y)
  on check(_X : RSA.Residue bits) → Bool
    return false

/-- **The systems of the RSA assumption** [1, §7]: `rsa-real`, and `Reject` on it, at the budget
`q` per port; `rsa-fake` is `Reject` on `rsa-real` (`RSA.Fake.perPort_eq_reject`). -/
def RSA.Assumption.systems (keyGen : Distribution.ProbDist (RSA.Key bits))
    (q : RSAChallenge.Port → ℕ) :
    Interface.Resource (RSAChallenge.perPort bits q) ×
      Interface.Resource (RSAChallenge.perPort bits q) :=
  (RSA.Real.perPort keyGen, RSA.Reject.perPort bits • RSA.Real.perPort keyGen)

/-- **The RSA assumption** within `error`: against the admitted distinguishers, `rsa-real`
substitutes for `rsa-fake`. -/
def RSA.Assumption [Interface.AdmissibleDistinguishers]
    (keyGen : Distribution.ProbDist (RSA.Key bits)) {q : RSAChallenge.Port → ℕ}
    (error : (RSAChallenge.perPort bits q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (RSA.Assumption.systems keyGen q).1 ≃[error] (RSA.Assumption.systems keyGen q).2

/-! ## Many challenges -/

-- `rsa*-real`: `(N, e, d) := RSA.KeyGen()`; `pk*()` returns `(N, e)`; `challenge*()` samples
-- `Y ← ℤ_N`, adds it to `𝒴` and returns it; `check*(X)` returns whether `X^e mod N ∈ 𝒴`.
system RSAStar.Real(keyGen : Distribution.ProbDist (RSA.Key bits)) : RSAStar bits
  initialize
    key ←$ keyGen
    challenges ← ([] : List (RSA.Residue bits))
  on pk() → RSA.Residue bits × RSA.Residue bits
    return (key.N, key.e)
  on challenge() → RSA.Residue bits
    Ys ←$ RSA.residues (bits := bits)
    challenges ← challenges ++ [Ys key.N]
    return Ys key.N
  on check(X : RSA.Residue bits) → Bool
    return decide (key.pow X key.e.val ∈ challenges)

-- `rsa*-fake`: as `rsa*-real`, but `check*(X)` returns `false`.
system RSAStar.Fake(keyGen : Distribution.ProbDist (RSA.Key bits)) : RSAStar bits
  initialize
    key ←$ keyGen
  on pk() → RSA.Residue bits × RSA.Residue bits
    return (key.N, key.e)
  on challenge() → RSA.Residue bits
    Ys ←$ RSA.residues (bits := bits)
    return Ys key.N
  on check(_X : RSA.Residue bits) → Bool
    return false

-- `Reject*`: forward `pk*()` and `challenge*()`, and answer every `check*(X)` with `false`.
converter RSAStar.Reject(bits : ℕ) : RSAStar bits
  inside rsa : RSAStar bits
  on pk() → RSA.Residue bits × RSA.Residue bits
    key ← rsa.pk()
    return key
  on challenge() → RSA.Residue bits
    Y ← rsa.challenge()
    return Y
  on check(_X : RSA.Residue bits) → Bool
    return false

/-- **The systems of the many-challenge RSA assumption** [1, §8]: `rsa*-real`, and `Reject*` on
it, at the budget `q` per port; `rsa*-fake` is `Reject*` on `rsa*-real`
(`RSAStar.Fake.perPort_eq_reject`). -/
def RSAStar.Assumption.systems (keyGen : Distribution.ProbDist (RSA.Key bits))
    (q : RSAStar.Port → ℕ) :
    Interface.Resource (RSAStar.perPort bits q) × Interface.Resource (RSAStar.perPort bits q) :=
  (RSAStar.Real.perPort keyGen, RSAStar.Reject.perPort bits • RSAStar.Real.perPort keyGen)

/-- **The many-challenge RSA assumption** within `error`: against the admitted distinguishers,
`rsa*-real` substitutes for `rsa*-fake`. -/
def RSAStar.Assumption [Interface.AdmissibleDistinguishers]
    (keyGen : Distribution.ProbDist (RSA.Key bits)) {q : RSAStar.Port → ℕ}
    (error : (RSAStar.perPort bits q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (RSAStar.Assumption.systems keyGen q).1 ≃[error] (RSAStar.Assumption.systems keyGen q).2

/-! ## Sampled functions

Every RSA library samples its key and its challenges once and answers deterministically, so it is
a sampled function. Indexed by their number, the many challenges of `rsa*` are a function on
`Fin n`, sampled once, and a root is checked against the first `k` challenges; `RSAStar.Count`
gives the `k`-th challenge the index `k` and checks a root against the challenges issued so far,
which is the many-challenge library of [1, §8]. -/

/-- **`rsa-real` as a sampled function**: the key `(N, e, d)` and the challenges `Y`, sampled
once. -/
def RSA.Real.sampled (keyGen : Distribution.ProbDist (RSA.Key bits))
    {q : RSAChallenge.Port → ℕ} : Interface.Resource (RSAChallenge.perPort bits q) :=
  Interface.Resource.sample (Distribution.prod keyGen.1 (RSA.residues (bits := bits)).1) fun kY =>
    Interface.Resource.ofFunction fun
      | .challenge => fun _ => (kY.1.N, kY.1.e, kY.2 kY.1.N)
      | .check => fun X => decide (kY.2 kY.1.N = kY.1.pow X kY.1.e.val)

/-- **`rsa-fake` as a sampled function**: as `rsa-real`, with every check rejected. -/
def RSA.Fake.sampled (keyGen : Distribution.ProbDist (RSA.Key bits))
    {q : RSAChallenge.Port → ℕ} : Interface.Resource (RSAChallenge.perPort bits q) :=
  Interface.Resource.sample (Distribution.prod keyGen.1 (RSA.residues (bits := bits)).1) fun kY =>
    Interface.Resource.ofFunction fun
      | .challenge => fun _ => (kY.1.N, kY.1.e, kY.2 kY.1.N)
      | .check => fun _ => false

/-- `rsa-real` is its sampled function. -/
lemma RSA.Real.perPort_eq_sampled (keyGen : Distribution.ProbDist (RSA.Key bits))
    (q : RSAChallenge.Port → ℕ) :
    RSA.Real.perPort keyGen (budget := q) = RSA.Real.sampled keyGen := by
  let real : RSA.Key bits × (RSA.Residue bits → RSA.Residue bits) →
      ∀ i, (RSAChallenge.perPort bits q).X i → (RSAChallenge.perPort bits q).Y i := fun kY => fun
    | .challenge => fun _ => (kY.1.N, kY.1.e, kY.2 kY.1.N)
    | .check => fun X => decide (kY.2 kY.1.N = kY.1.pow X kY.1.e.val)
  -- The system reads its two sources at the first invocation: the key and the challenges are
  -- the first entries of the source tables.
  rw [RSA.Real.perPort, RSA.Real.randomness, Resource.source, Resource.source, parallel_ofAutomaton,
    Converter.ofProgram_smul_ofAutomaton_eq_sample (A := RSAChallenge.perPort bits q) _ _ _ _ _ _
      (Distribution.prod (Distribution.pi fun _ => (RSA.Real.law1 keyGen).1)
        (Distribution.pi fun _ => (RSA.Real.law2 keyGen).1))
      (fun t => ((t.1, 0), (t.2, 0))) (Distribution.fTransform_prod _ _ _ _).symm
      (fun t => real (sourceEntry (RSA.Real.law1 keyGen) t.1 0,
        sourceEntry (RSA.Real.law2 keyGen) t.2 0))]
  · have entries := Resource.sample_fTransform (A := RSAChallenge.perPort bits q)
      (fun t : (Fin (RSA.Real.bound keyGen * ∑ i, q i) → RSA.Key bits) ×
        (Fin (RSA.Real.bound keyGen * ∑ i, q i) → RSA.Residue bits → RSA.Residue bits) =>
          (sourceEntry (RSA.Real.law1 keyGen) t.1 0, sourceEntry (RSA.Real.law2 keyGen) t.2 0))
      (Distribution.prod (Distribution.pi fun _ => (RSA.Real.law1 keyGen).1)
        (Distribution.pi fun _ => (RSA.Real.law2 keyGen).1))
      (fun kY => Resource.ofFunction (real kY))
    rw [← entries]
    by_cases hk : 0 < RSA.Real.bound keyGen * ∑ i, q i
    · refine Resource.sample_congr_law ?_ _
      change Distribution.fTransform (Prod.map (fun t => sourceEntry (RSA.Real.law1 keyGen) t 0)
        (fun t => sourceEntry (RSA.Real.law2 keyGen) t 0)) _ = _
      rw [Distribution.fTransform_prod, sourceEntry_zero_law _ hk, sourceEntry_zero_law _ hk]
      rfl
    · exact Resource.eq_of_not_domain fun h hd => hk
        (Nat.mul_pos (by norm_num [RSA.Real.bound]) (bound_pos_of_domain hd))
  · rintro ⟨t₁, t₂⟩
    refine automatonSystem_of_stored _ real _ (sourceEntry (RSA.Real.law1 keyGen) t₁ 0,
      sourceEntry (RSA.Real.law2 keyGen) t₂ 0) (fun i x => ⟨((t₁, 1), (t₂, 1)), ?_⟩)
      (fun r i x => ⟨r, ?_⟩)
    · refine Program.combine_eq_of_invoke _ _ (n := 2) ?_
      cases i <;> simp [Program.invoke, RSA.Real.body, callProg, returnProg, parallelStep,
        sourceStep, sourceEntry, real]
    · refine Program.combine_eq_of_invoke _ _ (n := 0) ?_
      cases i <;> simp [Program.invoke, RSA.Real.body, returnProg, real]

/-- `rsa-fake` is its sampled function. -/
lemma RSA.Fake.perPort_eq_sampled (keyGen : Distribution.ProbDist (RSA.Key bits))
    (q : RSAChallenge.Port → ℕ) :
    RSA.Fake.perPort keyGen (budget := q) = RSA.Fake.sampled keyGen := by
  let fake : RSA.Key bits × (RSA.Residue bits → RSA.Residue bits) →
      ∀ i, (RSAChallenge.perPort bits q).X i → (RSAChallenge.perPort bits q).Y i := fun kY => fun
    | .challenge => fun _ => (kY.1.N, kY.1.e, kY.2 kY.1.N)
    | .check => fun _ => false
  -- As `RSA.Real.perPort_eq_sampled`.
  rw [RSA.Fake.perPort, RSA.Fake.randomness, Resource.source, Resource.source, parallel_ofAutomaton,
    Converter.ofProgram_smul_ofAutomaton_eq_sample (A := RSAChallenge.perPort bits q) _ _ _ _ _ _
      (Distribution.prod (Distribution.pi fun _ => (RSA.Fake.law1 keyGen).1)
        (Distribution.pi fun _ => (RSA.Fake.law2 keyGen).1))
      (fun t => ((t.1, 0), (t.2, 0))) (Distribution.fTransform_prod _ _ _ _).symm
      (fun t => fake (sourceEntry (RSA.Fake.law1 keyGen) t.1 0,
        sourceEntry (RSA.Fake.law2 keyGen) t.2 0))]
  · have entries := Resource.sample_fTransform (A := RSAChallenge.perPort bits q)
      (fun t : (Fin (RSA.Fake.bound keyGen * ∑ i, q i) → RSA.Key bits) ×
        (Fin (RSA.Fake.bound keyGen * ∑ i, q i) → RSA.Residue bits → RSA.Residue bits) =>
          (sourceEntry (RSA.Fake.law1 keyGen) t.1 0, sourceEntry (RSA.Fake.law2 keyGen) t.2 0))
      (Distribution.prod (Distribution.pi fun _ => (RSA.Fake.law1 keyGen).1)
        (Distribution.pi fun _ => (RSA.Fake.law2 keyGen).1))
      (fun kY => Resource.ofFunction (fake kY))
    rw [← entries]
    by_cases hk : 0 < RSA.Fake.bound keyGen * ∑ i, q i
    · refine Resource.sample_congr_law ?_ _
      change Distribution.fTransform (Prod.map (fun t => sourceEntry (RSA.Fake.law1 keyGen) t 0)
        (fun t => sourceEntry (RSA.Fake.law2 keyGen) t 0)) _ = _
      rw [Distribution.fTransform_prod, sourceEntry_zero_law _ hk, sourceEntry_zero_law _ hk]
      rfl
    · exact Resource.eq_of_not_domain fun h hd => hk
        (Nat.mul_pos (by norm_num [RSA.Fake.bound]) (bound_pos_of_domain hd))
  · rintro ⟨t₁, t₂⟩
    refine automatonSystem_of_stored _ fake _ (sourceEntry (RSA.Fake.law1 keyGen) t₁ 0,
      sourceEntry (RSA.Fake.law2 keyGen) t₂ 0) (fun i x => ⟨((t₁, 1), (t₂, 1)), ?_⟩)
      (fun r i x => ⟨r, ?_⟩)
    · refine Program.combine_eq_of_invoke _ _ (n := 2) ?_
      cases i <;> simp [Program.invoke, RSA.Fake.body, callProg, returnProg, parallelStep,
        sourceStep, sourceEntry, fake]
    · refine Program.combine_eq_of_invoke _ _ (n := 0) ?_
      cases i <;> simp [Program.invoke, RSA.Fake.body, returnProg, fake]

/-- `A^e mod N` for residues `N, e, A`. -/
def RSA.powMod (N e A : RSA.Residue bits) : RSA.Residue bits :=
  ⟨A.val ^ e.val % N.val % 2 ^ bits, Nat.mod_lt _ (Nat.two_pow_pos bits)⟩

/-- `A^e mod N` at the key's `N` is the key's power. -/
lemma RSA.powMod_eq_pow (key : RSA.Key bits) (e A : RSA.Residue bits) :
    RSA.powMod key.N e A = key.pow A e.val :=
  Fin.ext (Nat.mod_eq_of_lt ((Nat.mod_lt _ key.2).trans key.N.isLt))

/-- The RSA library of the key `key`, the challenge `Y` and the check `chk`, as a function. -/
def RSA.library (key : RSA.Key bits) (Y : RSA.Residue bits) (chk : RSA.Residue bits → Bool) :
    ∀ j, (RSAChallenge bits 0).X j → (RSAChallenge bits 0).Y j
  | .challenge => fun _ => (key.N, key.e, Y)
  | .check => chk

/-- `rsa-real` as a sampled function, with its check: the RSA library of the key and the
challenge, checking `X^e ≡ Y (mod N)`. -/
lemma RSA.Real.sampled_eq_library (keyGen : Distribution.ProbDist (RSA.Key bits))
    (q : RSAChallenge.Port → ℕ) :
    RSA.Real.sampled keyGen (q := q) =
      Interface.Resource.sample (Distribution.prod keyGen.1 (RSA.residues (bits := bits)).1)
        fun kY => Interface.Resource.ofFunction (A := RSAChallenge.perPort bits q)
          (RSA.library kY.1 (kY.2 kY.1.N)
            fun X => decide (kY.2 kY.1.N = kY.1.pow X kY.1.e.val)) := by
  unfold RSA.Real.sampled
  congr 1
  funext kY
  congr 1
  funext i
  cases i <;> rfl

/-- `rsa-fake` as a sampled function, with its check: the RSA library of the key and the
challenge, rejecting every `X`. -/
lemma RSA.Fake.sampled_eq_library (keyGen : Distribution.ProbDist (RSA.Key bits))
    (q : RSAChallenge.Port → ℕ) :
    RSA.Fake.sampled keyGen (q := q) =
      Interface.Resource.sample (Distribution.prod keyGen.1 (RSA.residues (bits := bits)).1)
        fun kY => Interface.Resource.ofFunction (A := RSAChallenge.perPort bits q)
          (RSA.library kY.1 (kY.2 kY.1.N) fun _ => false) := by
  unfold RSA.Fake.sampled
  congr 1
  funext kY
  congr 1
  funext i
  cases i <;> rfl

/-- **`Reject` on an RSA library** rejects every `X`. -/
lemma RSA.Reject.smul_ofFunction (q : RSAChallenge.Port → ℕ) (key : RSA.Key bits)
    (Y : RSA.Residue bits) (chk : RSA.Residue bits → Bool) :
    RSA.Reject.perPort bits (budget := q) •
        Interface.Resource.ofFunction (A := RSAChallenge.perPort bits q) (RSA.library key Y chk) =
      Interface.Resource.ofFunction (A := RSAChallenge.perPort bits q)
        (RSA.library key Y fun _ => false) := by
  unfold RSA.Reject.perPort RSA.Reject.perPortProgram Interface.Converter.ofPreservingProgram
  refine Interface.ofDDC_ofProgramOn_smul_ofFunction (A := RSAChallenge.perPort bits q)
    (B := RSAChallenge.perPort bits q) none (RSA.Reject.body bits) (RSA.Reject.bound_spec bits) _
    _ _ fun t o x => ⟨some (), ?_⟩
  -- One call for `challenge`, none for `check`.
  cases o <;> cases t <;> simp [Program.answer, RSA.Reject.body, callProg, returnProg, RSA.library]

/-- **`rsa-fake` is `Reject` on `rsa-real`** [1, §7]. -/
theorem RSA.Fake.perPort_eq_reject (keyGen : Distribution.ProbDist (RSA.Key bits))
    (q : RSAChallenge.Port → ℕ) :
    RSA.Fake.perPort keyGen (budget := q) = RSA.Reject.perPort bits • RSA.Real.perPort keyGen := by
  rw [RSA.Fake.perPort_eq_sampled, RSA.Fake.sampled_eq_library, RSA.Real.perPort_eq_sampled,
    RSA.Real.sampled_eq_library, Resource.smul_sample]
  simp only [RSA.Reject.smul_ofFunction]

/-- **The RSA assumption from its sampled functions**: if `rsa-real` substitutes for `rsa-fake` as
sampled functions, the RSA assumption holds. -/
lemma RSA.Assumption.of_sampled [Interface.AdmissibleDistinguishers]
    (keyGen : Distribution.ProbDist (RSA.Key bits)) {q : RSAChallenge.Port → ℕ}
    {ε : (RSAChallenge.perPort bits q).inputDomain.DistinguisherBehavior → ENNReal}
    (secure : RSA.Real.sampled keyGen (q := q) ≃[ε] RSA.Fake.sampled keyGen) :
    RSA.Assumption keyGen ε := by
  show RSA.Real.perPort keyGen ≃[ε] RSA.Reject.perPort bits • RSA.Real.perPort keyGen
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    RSA.Real.perPort keyGen = RSA.Real.sampled keyGen := RSA.Real.perPort_eq_sampled keyGen q
    _ ≃[ε] RSA.Fake.sampled keyGen := secure
    _ = RSA.Fake.perPort keyGen := (RSA.Fake.perPort_eq_sampled keyGen q).symm
    _ = RSA.Reject.perPort bits • RSA.Real.perPort keyGen := RSA.Fake.perPort_eq_reject keyGen q

end

interface RSAIndexed(bits n : ℕ)
  pk() → RSA.Residue bits × RSA.Residue bits
  challenge(i : Fin n) → RSA.Residue bits
  check(k : Fin (n + 1), X : RSA.Residue bits) → Bool

noncomputable section

/-- **`rsa*-real`, indexed**: the key and `n` challenges `Y_i`, sampled once; `challenge(i)`
returns `Y_i` and `check(k, X)` whether `X^e ≡ Y_i (mod N)` for one of the first `k`
challenges. -/
def RSAStar.Indexed.real (keyGen : Distribution.ProbDist (RSA.Key bits)) (n : ℕ)
    {q : RSAIndexed.Port → ℕ} : Interface.Resource (RSAIndexed.perPort bits n q) :=
  Interface.Resource.sample (Distribution.prod keyGen.1
      (Distribution.ProbDist.pi fun _ : Fin n => RSA.residues (bits := bits)).1) fun kY =>
    Interface.Resource.ofFunction fun
      | .pk => fun _ => (kY.1.N, kY.1.e)
      | .challenge => fun i => kY.2 i kY.1.N
      | .check => fun kX =>
        decide (∃ i : Fin n, i.val < kX.1.val ∧ kY.1.pow kX.2 kY.1.e.val = kY.2 i kY.1.N)

/-- **`rsa*-fake`, indexed**: as `rsa*-real`, with every check rejected. -/
def RSAStar.Indexed.fake (keyGen : Distribution.ProbDist (RSA.Key bits)) (n : ℕ)
    {q : RSAIndexed.Port → ℕ} : Interface.Resource (RSAIndexed.perPort bits n q) :=
  Interface.Resource.sample (Distribution.prod keyGen.1
      (Distribution.ProbDist.pi fun _ : Fin n => RSA.residues (bits := bits)).1) fun kY =>
    Interface.Resource.ofFunction fun
      | .pk => fun _ => (kY.1.N, kY.1.e)
      | .challenge => fun i => kY.2 i kY.1.N
      | .check => fun _ => false

-- `Reject` for indexed challenges: forward `pk()` and `challenge(i)`, and answer every
-- `check(k, X)` with `false`.
converter RSAStar.Indexed.Reject(bits n : ℕ) : RSAIndexed bits n
  inside rsa : RSAIndexed bits n
  on pk() → RSA.Residue bits × RSA.Residue bits
    key ← rsa.pk()
    return key
  on challenge(i : Fin n) → RSA.Residue bits
    Y ← rsa.challenge(i)
    return Y
  on check(_k : Fin (n + 1), _X : RSA.Residue bits) → Bool
    return false

/-- **The systems of the indexed many-challenge RSA assumption**: the indexed `rsa*-real`, and
`Reject` on it, at the budget `q` per port; the indexed `rsa*-fake` is `Reject` on the indexed
`rsa*-real` (`RSAStar.Indexed.fake_eq_reject`). -/
def RSAStar.Indexed.systems (keyGen : Distribution.ProbDist (RSA.Key bits)) (n : ℕ)
    (q : RSAIndexed.Port → ℕ) :
    Interface.Resource (RSAIndexed.perPort bits n q) ×
      Interface.Resource (RSAIndexed.perPort bits n q) :=
  (RSAStar.Indexed.real keyGen n,
    RSAStar.Indexed.Reject.perPort bits n • RSAStar.Indexed.real keyGen n)

/-- **`Reject` on indexed challenges** rejects every root. -/
lemma RSAStar.Indexed.Reject.smul_ofFunction (n : ℕ) (q : RSAIndexed.Port → ℕ)
    (g : ∀ j, (RSAIndexed.perPort bits n q).X j → (RSAIndexed.perPort bits n q).Y j) :
    RSAStar.Indexed.Reject.perPort bits n • Interface.Resource.ofFunction g =
      Interface.Resource.ofFunction (A := RSAIndexed.perPort bits n q) fun
        | .pk => g .pk
        | .challenge => g .challenge
        | .check => fun _ => false := by
  unfold RSAStar.Indexed.Reject.perPort RSAStar.Indexed.Reject.perPortProgram
    Interface.Converter.ofPreservingProgram
  refine Interface.ofDDC_ofProgramOn_smul_ofFunction (A := RSAIndexed.perPort bits n q)
    (B := RSAIndexed.perPort bits n q) none (RSAStar.Indexed.Reject.body bits n)
    (RSAStar.Indexed.Reject.bound_spec bits n) _ g _ fun t o x => ⟨some (), ?_⟩
  -- One call for `pk` and `challenge`, none for `check`.
  cases o <;> cases t <;> simp [Program.answer, RSAStar.Indexed.Reject.body, callProg, returnProg]

/-- **The indexed `rsa*-fake` is `Reject` on the indexed `rsa*-real`.** -/
lemma RSAStar.Indexed.fake_eq_reject (keyGen : Distribution.ProbDist (RSA.Key bits)) (n : ℕ)
    (q : RSAIndexed.Port → ℕ) :
    RSAStar.Indexed.fake keyGen n (q := q) =
      RSAStar.Indexed.Reject.perPort bits n • RSAStar.Indexed.real keyGen n := by
  rw [RSAStar.Indexed.real, Resource.smul_sample, RSAStar.Indexed.fake]
  simp only [RSAStar.Indexed.Reject.smul_ofFunction]

/-- **The indexed many-challenge RSA assumption** within `error`: against the admitted
distinguishers, the indexed `rsa*-real` substitutes for the indexed `rsa*-fake`. -/
def RSAStar.Indexed [Interface.AdmissibleDistinguishers]
    (keyGen : Distribution.ProbDist (RSA.Key bits)) {n : ℕ} {q : RSAIndexed.Port → ℕ}
    (error : (RSAIndexed.perPort bits n q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (RSAStar.Indexed.systems keyGen n q).1 ≃[error] (RSAStar.Indexed.systems keyGen n q).2

end

-- `Count`: the `k`-th challenge is `indexed.challenge(k)`; `check*(X)` checks `X` against the
-- challenges issued so far.
converter RSAStar.Count(width n : ℕ) : RSAStar width
  inside indexed : RSAIndexed width n
  initialize
    issued ← (0 : ℕ)
  on pk() → RSA.Residue width × RSA.Residue width
    key ← indexed.pk()
    return key
  on challenge() → RSA.Residue width
    match (List.finRange n).find? fun k => k.val = issued
    | none →
      return ⟨0, Nat.two_pow_pos width⟩
    | some k →
      issued ← issued + 1
      Y ← indexed.challenge(k)
      return Y
  on check(X : RSA.Residue width) → Bool
    found ← indexed.check(Fin.ofNat (n + 1) (min issued n), X)
    return found

noncomputable section

/-- The automaton of `rsa*-real` against its sources, with tables of `k` entries. -/
local notation "realStep(" keyGen ", " k ")" =>
  Program.combine (RSAStar.Real.body keyGen) (parallelStep (sourceStep (q := k)
    (RSAStar.Real.law1 keyGen)) (sourceStep (q := k) (RSAStar.Real.law2 keyGen)))
    (RSAStar.Real.bound_spec keyGen)

/-- The automaton of `rsa*-fake` against its sources, with tables of `k` entries. -/
local notation "fakeStep(" keyGen ", " k ")" =>
  Program.combine (RSAStar.Fake.body keyGen) (parallelStep (sourceStep (q := k)
    (RSAStar.Fake.law1 keyGen)) (sourceStep (q := k) (RSAStar.Fake.law2 keyGen)))
    (RSAStar.Fake.bound_spec keyGen)

/-- The automaton of `Count` against the function `g`. -/
local notation "countStep(" width ", " n ", " g ")" =>
  Program.combine (RSAStar.Count.body width n) (fun (_ : Unit) j x => ((), g j x))
    (RSAStar.Count.bound_spec width n)

/-- `rsa*-real` against its sources: a first `pk()` reads the key. -/
lemma RSAStar.Real.combine_first_pk (keyGen : Distribution.ProbDist (RSA.Key bits)) {k : ℕ}
    (t₁ : Fin k → RSA.Key bits) (r : (Fin k → RSA.Residue bits → RSA.Residue bits) × ℕ) :
    realStep(keyGen, k) (none, ((t₁, 0), r)) .pk () =
      ((some (sourceEntry (RSAStar.Real.law1 keyGen) t₁ 0, []), ((t₁, 1), r)),
        ((sourceEntry (RSAStar.Real.law1 keyGen) t₁ 0).N,
          (sourceEntry (RSAStar.Real.law1 keyGen) t₁ 0).e)) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, RSAStar.Real.body, callProg, returnProg, parallelStep, sourceStep,
      sourceEntry])

/-- A first `challenge()` reads the key and the first challenge. -/
lemma RSAStar.Real.combine_first_challenge (keyGen : Distribution.ProbDist (RSA.Key bits)) {k : ℕ}
    (t₁ : Fin k → RSA.Key bits) (t₂ : Fin k → RSA.Residue bits → RSA.Residue bits) (c : ℕ) :
    realStep(keyGen, k) (none, ((t₁, 0), (t₂, c))) .challenge () =
      ((some (sourceEntry (RSAStar.Real.law1 keyGen) t₁ 0,
          [sourceEntry (RSAStar.Real.law2 keyGen) t₂ c
            (sourceEntry (RSAStar.Real.law1 keyGen) t₁ 0).N]),
        ((t₁, 1), (t₂, c + 1))),
        sourceEntry (RSAStar.Real.law2 keyGen) t₂ c
          (sourceEntry (RSAStar.Real.law1 keyGen) t₁ 0).N) :=
  Program.combine_eq_of_invoke _ _ (n := 2) (by
    simp [Program.invoke, RSAStar.Real.body, callProg, returnProg, parallelStep, sourceStep,
      sourceEntry])

/-- A first `check(X)` reads the key and rejects. -/
lemma RSAStar.Real.combine_first_check (keyGen : Distribution.ProbDist (RSA.Key bits)) {k : ℕ}
    (t₁ : Fin k → RSA.Key bits) (r : (Fin k → RSA.Residue bits → RSA.Residue bits) × ℕ)
    (X : RSA.Residue bits) :
    realStep(keyGen, k) (none, ((t₁, 0), r)) .check X =
      ((some (sourceEntry (RSAStar.Real.law1 keyGen) t₁ 0, []), ((t₁, 1), r)), false) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, RSAStar.Real.body, callProg, returnProg, parallelStep, sourceStep,
      sourceEntry])

/-- Once the key is stored, `pk()` returns it. -/
lemma RSAStar.Real.combine_later_pk (keyGen : Distribution.ProbDist (RSA.Key bits)) {k : ℕ}
    (key : RSA.Key bits)
    (ch : List (RSA.Residue bits)) (r : ((Fin k → RSA.Key bits) × ℕ) ×
      ((Fin k → RSA.Residue bits → RSA.Residue bits) × ℕ)) :
    realStep(keyGen, k) (some (key, ch), r) .pk () = ((some (key, ch), r), (key.N, key.e)) :=
  Program.combine_eq_of_invoke _ _ (n := 0) (by
    simp [Program.invoke, RSAStar.Real.body, returnProg])

/-- Once the key is stored, `challenge()` reads the next challenge. -/
lemma RSAStar.Real.combine_later_challenge (keyGen : Distribution.ProbDist (RSA.Key bits)) {k : ℕ}
    (key : RSA.Key bits) (ch : List (RSA.Residue bits)) (r₁ : (Fin k → RSA.Key bits) × ℕ)
    (t₂ : Fin k → RSA.Residue bits → RSA.Residue bits) (c : ℕ) :
    realStep(keyGen, k) (some (key, ch), (r₁, (t₂, c))) .challenge () =
      ((some (key, ch ++ [sourceEntry (RSAStar.Real.law2 keyGen) t₂ c key.N]), (r₁, (t₂, c + 1))),
        sourceEntry (RSAStar.Real.law2 keyGen) t₂ c key.N) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, RSAStar.Real.body, callProg, returnProg, parallelStep, sourceStep,
      sourceEntry])

/-- Once the key is stored, `check(X)` checks `X` against the challenges so far. -/
lemma RSAStar.Real.combine_later_check (keyGen : Distribution.ProbDist (RSA.Key bits)) {k : ℕ}
    (key : RSA.Key bits) (ch : List (RSA.Residue bits)) (r : ((Fin k → RSA.Key bits) × ℕ) ×
      ((Fin k → RSA.Residue bits → RSA.Residue bits) × ℕ)) (X : RSA.Residue bits) :
    realStep(keyGen, k) (some (key, ch), r) .check X =
      ((some (key, ch), r), decide (key.pow X key.e.val ∈ ch)) :=
  Program.combine_eq_of_invoke _ _ (n := 0) (by
    simp [Program.invoke, RSAStar.Real.body, returnProg])

/-- `rsa*-fake` against its sources: a first `pk()` reads the key. -/
lemma RSAStar.Fake.combine_first_pk (keyGen : Distribution.ProbDist (RSA.Key bits)) {k : ℕ}
    (t₁ : Fin k → RSA.Key bits) (r : (Fin k → RSA.Residue bits → RSA.Residue bits) × ℕ) :
    fakeStep(keyGen, k)
        (none, ((t₁, 0), r)) .pk () =
      ((some (sourceEntry (RSAStar.Fake.law1 keyGen) t₁ 0), ((t₁, 1), r)),
        ((sourceEntry (RSAStar.Fake.law1 keyGen) t₁ 0).N,
          (sourceEntry (RSAStar.Fake.law1 keyGen) t₁ 0).e)) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, RSAStar.Fake.body, callProg, returnProg, parallelStep, sourceStep,
      sourceEntry])

/-- A first `challenge()` reads the key and the first challenge. -/
lemma RSAStar.Fake.combine_first_challenge (keyGen : Distribution.ProbDist (RSA.Key bits)) {k : ℕ}
    (t₁ : Fin k → RSA.Key bits) (t₂ : Fin k → RSA.Residue bits → RSA.Residue bits) (c : ℕ) :
    fakeStep(keyGen, k)
        (none, ((t₁, 0), (t₂, c))) .challenge () =
      ((some (sourceEntry (RSAStar.Fake.law1 keyGen) t₁ 0), ((t₁, 1), (t₂, c + 1))),
        sourceEntry (RSAStar.Fake.law2 keyGen) t₂ c
          (sourceEntry (RSAStar.Fake.law1 keyGen) t₁ 0).N) :=
  Program.combine_eq_of_invoke _ _ (n := 2) (by
    simp [Program.invoke, RSAStar.Fake.body, callProg, returnProg, parallelStep, sourceStep,
      sourceEntry])

/-- A first `check(X)` reads the key and rejects. -/
lemma RSAStar.Fake.combine_first_check (keyGen : Distribution.ProbDist (RSA.Key bits)) {k : ℕ}
    (t₁ : Fin k → RSA.Key bits) (r : (Fin k → RSA.Residue bits → RSA.Residue bits) × ℕ)
    (X : RSA.Residue bits) :
    fakeStep(keyGen, k)
        (none, ((t₁, 0), r)) .check X =
      ((some (sourceEntry (RSAStar.Fake.law1 keyGen) t₁ 0), ((t₁, 1), r)), false) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, RSAStar.Fake.body, callProg, returnProg, parallelStep, sourceStep,
      sourceEntry])

/-- Once the key is stored, `pk()` returns it. -/
lemma RSAStar.Fake.combine_later_pk (keyGen : Distribution.ProbDist (RSA.Key bits)) {k : ℕ}
    (key : RSA.Key bits)
    (r : ((Fin k → RSA.Key bits) × ℕ) × ((Fin k → RSA.Residue bits → RSA.Residue bits) × ℕ)) :
    fakeStep(keyGen, k)
        (some key, r) .pk () = ((some key, r), (key.N, key.e)) :=
  Program.combine_eq_of_invoke _ _ (n := 0) (by
    simp [Program.invoke, RSAStar.Fake.body, returnProg])

/-- Once the key is stored, `challenge()` reads the next challenge. -/
lemma RSAStar.Fake.combine_later_challenge (keyGen : Distribution.ProbDist (RSA.Key bits)) {k : ℕ}
    (key : RSA.Key bits) (r₁ : (Fin k → RSA.Key bits) × ℕ)
    (t₂ : Fin k → RSA.Residue bits → RSA.Residue bits) (c : ℕ) :
    fakeStep(keyGen, k)
        (some key, (r₁, (t₂, c))) .challenge () =
      ((some key, (r₁, (t₂, c + 1))), sourceEntry (RSAStar.Fake.law2 keyGen) t₂ c key.N) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, RSAStar.Fake.body, callProg, returnProg, parallelStep, sourceStep,
      sourceEntry])

/-- Once the key is stored, `check(X)` rejects. -/
lemma RSAStar.Fake.combine_later_check (keyGen : Distribution.ProbDist (RSA.Key bits)) {k : ℕ}
    (key : RSA.Key bits)
    (r : ((Fin k → RSA.Key bits) × ℕ) × ((Fin k → RSA.Residue bits → RSA.Residue bits) × ℕ))
    (X : RSA.Residue bits) :
    fakeStep(keyGen, k)
        (some key, r) .check X = ((some key, r), false) :=
  Program.combine_eq_of_invoke _ _ (n := 0) (by
    simp [Program.invoke, RSAStar.Fake.body, returnProg])

/-- `Count` against a function: `pk()` is forwarded. -/
lemma RSAStar.Count.combine_pk (width n : ℕ)
    (g : ∀ j, RSAIndexed.Input width n j → RSAIndexed.Output width j)
    (st : Option ℕ) :
    countStep(width, n, g) (st, ()) .pk () = ((some (st.getD 0), ()), g .pk ()) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    cases st <;> simp [Program.invoke, RSAStar.Count.body, callProg, returnProg])

/-- `Count` against a function: the `c`-th challenge is the indexed one at `c`. -/
lemma RSAStar.Count.combine_challenge (width n : ℕ)
    (g : ∀ j, RSAIndexed.Input width n j → RSAIndexed.Output width j) (st : Option ℕ)
    (h : st.getD 0 < n) :
    countStep(width, n, g) (st, ()) .challenge () =
      ((some (st.getD 0 + 1), ()), g .challenge ⟨st.getD 0, h⟩) := by
  refine Program.combine_eq_of_invoke _ _ (n := 1) ?_
  cases st <;> simp only [Option.getD] at h ⊢ <;>
    simp [Program.invoke, RSAStar.Count.body, callProg, returnProg, List.find?_finRange_val, h]

/-- `Count` against a function: `check(X)` against the challenges issued so far. -/
lemma RSAStar.Count.combine_check (width n : ℕ)
    (g : ∀ j, RSAIndexed.Input width n j → RSAIndexed.Output width j) (st : Option ℕ)
    (X : RSA.Residue width) :
    countStep(width, n, g) (st, ()) .check X =
      ((some (st.getD 0), ()), g .check (Fin.ofNat (n + 1) (min (st.getD 0) n), X)) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    cases st <;> simp [Program.invoke, RSAStar.Count.body, callProg, returnProg])

/-- **`rsa*-real` is the indexed one, counted**: with an index for each challenge query. -/
lemma RSAStar.Real.perPort_eq_count (keyGen : Distribution.ProbDist (RSA.Key bits))
    (q : RSAStar.Port → ℕ) :
    RSAStar.Real.perPort keyGen (budget := q) =
      RSAStar.Count.perPort bits (q .challenge) • RSAStar.Indexed.real keyGen (q .challenge) := by
  -- The `k`-th fresh challenge is the `k`-th entry of a table of independent challenges, and the
  -- issued challenges are the first entries.
  classical
  rw [RSAStar.Real.perPort, RSAStar.Real.randomness, Resource.source, Resource.source,
    parallel_ofAutomaton, Converter.ofProgram_smul_ofAutomaton]
  erw [Resource.ofAutomaton_fTransform]
  -- The law of the two tables, and the indexed function the system answers by.
  have hlaw : Distribution.prod
      (Distribution.fTransform (fun t => (t, 0))
        (Distribution.pi fun _ : Fin (RSAStar.Real.bound keyGen * ∑ i, q i) =>
          (RSAStar.Real.law1 keyGen).1))
      (Distribution.fTransform (fun t => (t, 0))
        (Distribution.pi fun _ : Fin (RSAStar.Real.bound keyGen * ∑ i, q i) =>
          (RSAStar.Real.law2 keyGen).1)) =
      Distribution.fTransform (fun t => ((t.1, 0), (t.2, 0)))
        (Distribution.prod (Distribution.pi fun _ => (RSAStar.Real.law1 keyGen).1)
          (Distribution.pi fun _ => (RSAStar.Real.law2 keyGen).1)) :=
    (Distribution.fTransform_prod _ _ _ _).symm
  erw [Resource.sample_congr_law hlaw, Resource.sample_fTransform]
  rw [RSAStar.Indexed.real, Resource.smul_sample]
  have hmn : q .challenge ≤ RSAStar.Real.bound keyGen * ∑ i, q i :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ RSAStar.Port.challenge)).trans
      (Nat.le_mul_of_pos_left _ (by norm_num [RSAStar.Real.bound]))
  by_cases hk : 0 < RSAStar.Real.bound keyGen * ∑ i, q i
  swap
  · exact Resource.eq_of_not_domain fun h hd => hk
      (Nat.mul_pos (by norm_num [RSAStar.Real.bound]) (bound_pos_of_domain hd))
  refine Resource.sample_eq_sample_of_fTransform _ _
    (fun t => (sourceEntry (RSAStar.Real.law1 keyGen) t.1 0,
      fun i : Fin (q .challenge) => t.2 (Fin.castLE hmn i))) _ _ ?_ ?_
  · change Distribution.fTransform (Prod.map (fun t => sourceEntry (RSAStar.Real.law1 keyGen) t 0)
      (fun (t : Fin (RSAStar.Real.bound keyGen * ∑ i, q i) → RSA.Residue bits → RSA.Residue bits)
        (i : Fin (q .challenge)) => t (Fin.castLE hmn i))) _ = _
    rw [Distribution.fTransform_prod, sourceEntry_zero_law _ hk,
      Distribution.fTransform_pi_castLE _ (RSAStar.Real.law2 keyGen).2.2]
    rfl
  · rintro ⟨t₁, t₂⟩
    dsimp only
    rw [RSAStar.Count.perPort, RSAStar.Count.perPortProgram,
      Converter.ofPreservingProgram_smul_ofFunction]
    -- The key is read at the first query, the `c`-th challenge at the `c`-th challenge query.
    have entry : ∀ c (hc : c < q .challenge), sourceEntry (RSAStar.Real.law2 keyGen) t₂ c =
        t₂ (Fin.castLE hmn ⟨c, hc⟩) := by
      intro c hc
      simp only [sourceEntry, sourceStep]
      rw [dif_pos (hc.trans_le hmn)]
      rfl
    refine Resource.ofAutomaton_single_congr_on_domain (fun h
      (sL : Option (RSA.Key bits × List (RSA.Residue bits)) ×
        (((Fin (RSAStar.Real.bound keyGen * ∑ i, q i) → RSA.Key bits) × ℕ) ×
          ((Fin (RSAStar.Real.bound keyGen * ∑ i, q i) → RSA.Residue bits → RSA.Residue bits) × ℕ)))
      (sR : Option ℕ × Unit) =>
        sL.2.1.1 = t₁ ∧ sL.2.2 = (t₂, (SystemAlgebra.restrict RSAStar.Port.challenge h).length) ∧
          (sR.1.getD 0 : ℕ) = (SystemAlgebra.restrict RSAStar.Port.challenge h).length ∧
          ((h = [] ∧ sL.1 = none ∧ sL.2.1.2 = 0) ∨
            (h ≠ [] ∧ sL.1 = some (sourceEntry (RSAStar.Real.law1 keyGen) t₁ 0,
              (List.range (SystemAlgebra.restrict RSAStar.Port.challenge h).length).map fun c =>
                sourceEntry (RSAStar.Real.law2 keyGen) t₂ c
                  (sourceEntry (RSAStar.Real.law1 keyGen) t₁ 0).N) ∧ sL.2.1.2 = 1)))
      ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩ ?_
    rintro h ⟨i, x⟩ ⟨stL, ⟨t₁', c₁⟩, ⟨t₂', c₂⟩⟩ ⟨(stR : Option ℕ), ⟨⟩⟩ hd ⟨rfl, hr, hR, hcase⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
    have hj := hd.2 RSAStar.Port.challenge
    dsimp only at hR hcase ⊢
    cases i
    · -- `pk()`: the public key.
      cases x
      rw [RSAStar.Count.combine_pk]
      rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨hne, rfl, rfl⟩
      · rw [RSAStar.Real.combine_first_pk]
        refine ⟨rfl, rfl, by simp, by simp [hR], Or.inr ⟨by simp, by simp, rfl⟩⟩
      · rw [RSAStar.Real.combine_later_pk]
        refine ⟨rfl, rfl, by simp, by simp [hR], Or.inr ⟨by simp, by simp, rfl⟩⟩
    · -- `challenge()`: the next challenge.
      cases x
      have hlt : (SystemAlgebra.restrict RSAStar.Port.challenge h).length < q .challenge := by
        simpa using hj
      rw [RSAStar.Count.combine_challenge _ _ _ _ (hR ▸ hlt)]
      rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨hne, rfl, rfl⟩
      · rw [RSAStar.Real.combine_first_challenge]
        refine ⟨?_, rfl, by simp, by simp [hR], Or.inr ⟨by simp, by simp, rfl⟩⟩
        simp only [hR, SystemAlgebra.restrict_nil, List.length_nil] at hlt ⊢
        rw [entry 0 hlt]
      · rw [RSAStar.Real.combine_later_challenge]
        refine ⟨?_, rfl, by simp, by simp [hR], Or.inr ⟨by simp, ?_, rfl⟩⟩
        · simp only [hR]
          rw [entry _ hlt]
        · simp [List.range_succ]
    · -- `check(X)`: a root of one of the challenges so far.
      have hle : (SystemAlgebra.restrict RSAStar.Port.challenge h).length ≤ q .challenge := by
        simpa using hj
      rw [RSAStar.Count.combine_check]
      rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨hne, rfl, rfl⟩
      · rw [RSAStar.Real.combine_first_check]
        refine ⟨?_, rfl, by simp, by simp [hR], Or.inr ⟨by simp, by simp, rfl⟩⟩
        simp [hR]
      · rw [RSAStar.Real.combine_later_check]
        refine ⟨?_, rfl, by simp, by simp [hR], Or.inr ⟨by simp, by simp, rfl⟩⟩
        simp only [hR, Fin.val_ofNat, Nat.min_eq_left hle,
          Nat.mod_eq_of_lt (Nat.lt_succ_of_le hle)]
        rw [decide_eq_decide]
        simp only [List.mem_map, List.mem_range]
        constructor
        · rintro ⟨c, hc, he⟩
          exact ⟨⟨c, hc.trans_le hle⟩, hc, by rw [← he, entry c (hc.trans_le hle)]⟩
        · rintro ⟨i, hi, he⟩
          exact ⟨i.val, hi, by rw [entry i.val i.isLt, he]⟩

/-- **`rsa*-fake` is the indexed one, counted.** -/
lemma RSAStar.Fake.perPort_eq_count (keyGen : Distribution.ProbDist (RSA.Key bits))
    (q : RSAStar.Port → ℕ) :
    RSAStar.Fake.perPort keyGen (budget := q) =
      RSAStar.Count.perPort bits (q .challenge) • RSAStar.Indexed.fake keyGen (q .challenge) := by
  -- As `RSAStar.Real.perPort_eq_count`.
  classical
  rw [RSAStar.Fake.perPort, RSAStar.Fake.randomness, Resource.source, Resource.source,
    parallel_ofAutomaton, Converter.ofProgram_smul_ofAutomaton]
  erw [Resource.ofAutomaton_fTransform]
  -- The law of the two tables, and the indexed function the system answers by.
  have hlaw : Distribution.prod
      (Distribution.fTransform (fun t => (t, 0))
        (Distribution.pi fun _ : Fin (RSAStar.Fake.bound keyGen * ∑ i, q i) =>
          (RSAStar.Fake.law1 keyGen).1))
      (Distribution.fTransform (fun t => (t, 0))
        (Distribution.pi fun _ : Fin (RSAStar.Fake.bound keyGen * ∑ i, q i) =>
          (RSAStar.Fake.law2 keyGen).1)) =
      Distribution.fTransform (fun t => ((t.1, 0), (t.2, 0)))
        (Distribution.prod (Distribution.pi fun _ => (RSAStar.Fake.law1 keyGen).1)
          (Distribution.pi fun _ => (RSAStar.Fake.law2 keyGen).1)) :=
    (Distribution.fTransform_prod _ _ _ _).symm
  erw [Resource.sample_congr_law hlaw, Resource.sample_fTransform]
  rw [RSAStar.Indexed.fake, Resource.smul_sample]
  have hmn : q .challenge ≤ RSAStar.Fake.bound keyGen * ∑ i, q i :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ RSAStar.Port.challenge)).trans
      (Nat.le_mul_of_pos_left _ (by norm_num [RSAStar.Fake.bound]))
  by_cases hk : 0 < RSAStar.Fake.bound keyGen * ∑ i, q i
  swap
  · exact Resource.eq_of_not_domain fun h hd => hk
      (Nat.mul_pos (by norm_num [RSAStar.Fake.bound]) (bound_pos_of_domain hd))
  refine Resource.sample_eq_sample_of_fTransform _ _
    (fun t => (sourceEntry (RSAStar.Fake.law1 keyGen) t.1 0,
      fun i : Fin (q .challenge) => t.2 (Fin.castLE hmn i))) _ _ ?_ ?_
  · change Distribution.fTransform (Prod.map (fun t => sourceEntry (RSAStar.Fake.law1 keyGen) t 0)
      (fun (t : Fin (RSAStar.Fake.bound keyGen * ∑ i, q i) → RSA.Residue bits → RSA.Residue bits)
        (i : Fin (q .challenge)) => t (Fin.castLE hmn i))) _ = _
    rw [Distribution.fTransform_prod, sourceEntry_zero_law _ hk,
      Distribution.fTransform_pi_castLE _ (RSAStar.Fake.law2 keyGen).2.2]
    rfl
  · rintro ⟨t₁, t₂⟩
    dsimp only
    rw [RSAStar.Count.perPort, RSAStar.Count.perPortProgram,
      Converter.ofPreservingProgram_smul_ofFunction]
    -- The key is read at the first query, the `c`-th challenge at the `c`-th challenge query.
    have entry : ∀ c (hc : c < q .challenge), sourceEntry (RSAStar.Fake.law2 keyGen) t₂ c =
        t₂ (Fin.castLE hmn ⟨c, hc⟩) := by
      intro c hc
      simp only [sourceEntry, sourceStep]
      rw [dif_pos (hc.trans_le hmn)]
      rfl
    refine Resource.ofAutomaton_single_congr_on_domain (fun h
      (sL : Option (RSA.Key bits) ×
        (((Fin (RSAStar.Fake.bound keyGen * ∑ i, q i) → RSA.Key bits) × ℕ) ×
          ((Fin (RSAStar.Fake.bound keyGen * ∑ i, q i) → RSA.Residue bits → RSA.Residue bits) × ℕ)))
      (sR : Option ℕ × Unit) =>
        sL.2.1.1 = t₁ ∧ sL.2.2 = (t₂, (SystemAlgebra.restrict RSAStar.Port.challenge h).length) ∧
          (sR.1.getD 0 : ℕ) = (SystemAlgebra.restrict RSAStar.Port.challenge h).length ∧
          ((h = [] ∧ sL.1 = none ∧ sL.2.1.2 = 0) ∨
            (h ≠ [] ∧ sL.1 = some (sourceEntry (RSAStar.Fake.law1 keyGen) t₁ 0) ∧ sL.2.1.2 = 1)))
      ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩ ?_
    rintro h ⟨i, x⟩ ⟨stL, ⟨t₁', c₁⟩, ⟨t₂', c₂⟩⟩ ⟨(stR : Option ℕ), ⟨⟩⟩ hd ⟨rfl, hr, hR, hcase⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
    have hj := hd.2 RSAStar.Port.challenge
    dsimp only at hR hcase ⊢
    cases i
    · -- `pk()`: the public key.
      cases x
      rw [RSAStar.Count.combine_pk]
      rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨hne, rfl, rfl⟩
      · rw [RSAStar.Fake.combine_first_pk]
        refine ⟨rfl, rfl, by simp, by simp [hR], Or.inr ⟨by simp, by simp, rfl⟩⟩
      · rw [RSAStar.Fake.combine_later_pk]
        refine ⟨rfl, rfl, by simp, by simp [hR], Or.inr ⟨by simp, by simp, rfl⟩⟩
    · -- `challenge()`: the next challenge.
      cases x
      have hlt : (SystemAlgebra.restrict RSAStar.Port.challenge h).length < q .challenge := by
        simpa using hj
      rw [RSAStar.Count.combine_challenge _ _ _ _ (hR ▸ hlt)]
      rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨hne, rfl, rfl⟩
      · rw [RSAStar.Fake.combine_first_challenge]
        refine ⟨?_, rfl, by simp, by simp [hR], Or.inr ⟨by simp, by simp, rfl⟩⟩
        simp only [hR, SystemAlgebra.restrict_nil, List.length_nil] at hlt ⊢
        rw [entry 0 hlt]
      · rw [RSAStar.Fake.combine_later_challenge]
        refine ⟨?_, rfl, by simp, by simp [hR], Or.inr ⟨by simp, ?_, rfl⟩⟩
        · simp only [hR]
          rw [entry _ hlt]
        · rfl
    · -- `check(X)`: rejected.
      rw [RSAStar.Count.combine_check]
      rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨hne, rfl, rfl⟩
      · rw [RSAStar.Fake.combine_first_check]
        exact ⟨rfl, rfl, by simp, by simp [hR], Or.inr ⟨by simp, rfl, rfl⟩⟩
      · rw [RSAStar.Fake.combine_later_check]
        exact ⟨rfl, rfl, by simp, by simp [hR], Or.inr ⟨by simp, rfl, rfl⟩⟩

/-- `Reject*` against a deterministic step: `pk*()` is forwarded. -/
lemma RSAStar.Reject.combine_pk {R : Type}
    (step : R → (j : RSAStar.Port) → RSAStar.Input bits j → R × RSAStar.Output bits j)
    (s : Option Unit) (r : R) :
    (RSAStar.Reject.body bits).combine step (RSAStar.Reject.bound_spec bits) (s, r) .pk () =
      ((some (), (step r .pk ()).1), (step r .pk ()).2) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    cases s <;> simp [Program.invoke, RSAStar.Reject.body, callProg, returnProg])

/-- `Reject*` against a deterministic step: `challenge*()` is forwarded. -/
lemma RSAStar.Reject.combine_challenge {R : Type}
    (step : R → (j : RSAStar.Port) → RSAStar.Input bits j → R × RSAStar.Output bits j)
    (s : Option Unit) (r : R) :
    (RSAStar.Reject.body bits).combine step (RSAStar.Reject.bound_spec bits) (s, r) .challenge
        () = ((some (), (step r .challenge ()).1), (step r .challenge ()).2) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    cases s <;> simp [Program.invoke, RSAStar.Reject.body, callProg, returnProg])

/-- `Reject*` against a deterministic step: `check*(X)` is rejected without a call. -/
lemma RSAStar.Reject.combine_check {R : Type}
    (step : R → (j : RSAStar.Port) → RSAStar.Input bits j → R × RSAStar.Output bits j)
    (s : Option Unit) (r : R) (X : RSA.Residue bits) :
    (RSAStar.Reject.body bits).combine step (RSAStar.Reject.bound_spec bits) (s, r) .check X =
      ((some (), r), false) :=
  Program.combine_eq_of_invoke _ _ (n := 0) (by
    cases s <;> simp [Program.invoke, RSAStar.Reject.body, returnProg])

/-- **`Reject*` after `Count` is `Count` after `Reject`**, on the indexed challenges of a
function: both count the challenges alike, and reject every root. -/
lemma RSAStar.Reject.smul_count (n : ℕ) (q : RSAStar.Port → ℕ)
    (g : ∀ j, RSAIndexed.Input bits n j → RSAIndexed.Output bits j) (hn : q .challenge ≤ n) :
    RSAStar.Reject.perPort bits (budget := q) • (RSAStar.Count.perPort bits n •
        Resource.ofFunction
          (A := RSAIndexed.perPort bits n (RSAStar.Count.insideBudget bits n q)) g) =
      RSAStar.Count.perPort bits n • Resource.ofFunction
        (A := RSAIndexed.perPort bits n (RSAStar.Count.insideBudget bits n q)) fun
          | .pk => g .pk
          | .challenge => g .challenge
          | .check => fun _ => false := by
  rw [RSAStar.Count.perPort, RSAStar.Count.perPortProgram,
    Converter.ofPreservingProgram_smul_ofFunction, Converter.ofPreservingProgram_smul_ofFunction,
    RSAStar.Reject.perPort, RSAStar.Reject.perPortProgram,
    Converter.ofPreservingProgram_smul_ofAutomaton]
  rw [show (⟨Distribution.fTransform (fun r => (none, r))
      (Distribution.ProbDist.single ((none : Option ℕ), ())).1, _⟩ :
        Distribution.ProbDist (Option Unit × (Option ℕ × Unit))) =
      Distribution.ProbDist.single (none, (none, ())) from Subtype.ext Finsupp.mapDomain_single]
  -- The two counts of the challenges issued agree, and are the number of challenge queries.
  refine Resource.ofAutomaton_single_congr_on_domain (fun h
      (sL : Option Unit × (Option ℕ × Unit)) (sR : Option ℕ × Unit) =>
        sL.2.1.getD 0 = (SystemAlgebra.restrict RSAStar.Port.challenge h).length ∧
          sR.1.getD 0 = (SystemAlgebra.restrict RSAStar.Port.challenge h).length)
    ⟨rfl, rfl⟩ ?_
  rintro h ⟨i, x⟩ ⟨sRej, (st : Option ℕ), ⟨⟩⟩ ⟨(st' : Option ℕ), ⟨⟩⟩ hd ⟨hL, hR⟩
  have hj := hd.2 RSAStar.Port.challenge
  dsimp only at hL hR ⊢
  cases i
  · -- `pk*()`: forwarded.
    cases x
    rw [RSAStar.Reject.combine_pk, RSAStar.Count.combine_pk, RSAStar.Count.combine_pk]
    exact ⟨rfl, by simp [hL], by simp [hR]⟩
  · -- `challenge*()`: the next indexed challenge on both sides.
    cases x
    have hlt : (SystemAlgebra.restrict RSAStar.Port.challenge h).length < n :=
      (by simpa using hj : (SystemAlgebra.restrict RSAStar.Port.challenge h).length < q .challenge)
        |>.trans_le hn
    rw [RSAStar.Reject.combine_challenge, RSAStar.Count.combine_challenge _ _ _ _ (hL ▸ hlt),
      RSAStar.Count.combine_challenge _ _ _ _ (hR ▸ hlt)]
    refine ⟨by simp only [hL, hR], by simp [hL], by simp [hR]⟩
  · -- `check*(X)`: rejected on both sides.
    rw [RSAStar.Reject.combine_check, RSAStar.Count.combine_check]
    exact ⟨rfl, by simpa using hL, by simpa using hR⟩

/-- **`rsa*-fake` is `Reject*` on `rsa*-real`** [1, §8]. -/
theorem RSAStar.Fake.perPort_eq_reject (keyGen : Distribution.ProbDist (RSA.Key bits))
    (q : RSAStar.Port → ℕ) :
    RSAStar.Fake.perPort keyGen (budget := q) =
      RSAStar.Reject.perPort bits • RSAStar.Real.perPort keyGen := by
  rw [RSAStar.Fake.perPort_eq_count, RSAStar.Real.perPort_eq_count,
    RSAStar.Indexed.fake_eq_reject, RSAStar.Indexed.real, Resource.smul_sample,
    Resource.smul_sample, Resource.smul_sample, Resource.smul_sample]
  congr 1
  funext kY
  rw [RSAStar.Indexed.Reject.smul_ofFunction, RSAStar.Reject.smul_count _ _ _ le_rfl]
  congr 2
  funext j
  cases j <;> rfl

end

/-! ## Units modulo `N` -/

noncomputable section

/-- `x · y mod N`. -/
def RSA.mulMod (N x y : RSA.Residue bits) : RSA.Residue bits :=
  ⟨x.val * y.val % N.val % 2 ^ bits, Nat.mod_lt _ (Nat.two_pow_pos bits)⟩

/-- `x⁻¹ mod N`, for a unit `x` modulo `N`. -/
def RSA.invMod (N x : RSA.Residue bits) : RSA.Residue bits :=
  ⟨((x.val : ZMod N.val)⁻¹).val % 2 ^ bits, Nat.mod_lt _ (Nat.two_pow_pos bits)⟩

/-- `x` is a unit modulo `N`: a residue modulo `N` coprime to it. -/
def RSA.IsUnit (N x : RSA.Residue bits) : Prop :=
  x.val < N.val ∧ x.val.Coprime N.val

instance RSA.nonempty_residues (N : RSA.Residue bits) :
    Nonempty {y : RSA.Residue bits // y.val < max N.val 1} :=
  ⟨⟨⟨0, Nat.two_pow_pos bits⟩, lt_max_of_lt_right Nat.one_pos⟩⟩

instance RSA.decidableIsUnit (N : RSA.Residue bits) : DecidablePred (RSA.IsUnit N) :=
  fun x => inferInstanceAs (Decidable (x.val < N.val ∧ x.val.Coprime N.val))

instance RSA.nonempty_units (N : RSA.Residue bits) :
    Nonempty {y : RSA.Residue bits // y.val < max N.val 1 ∧ y.val.Coprime (max N.val 1)} :=
  ⟨⟨⟨1 % max N.val 1, (Nat.mod_lt _ (lt_max_of_lt_right Nat.one_pos)).trans_le
      (max_le N.isLt.le (Nat.one_le_two_pow))⟩,
    Nat.mod_lt _ (lt_max_of_lt_right Nat.one_pos), by simp [Nat.Coprime]⟩⟩

/-- **The uniform law on the units modulo `N`**, modulo `max N 1`. -/
def RSA.unit (N : RSA.Residue bits) : Distribution.ProbDist (RSA.Residue bits) :=
  Distribution.ProbDist.map Subtype.val
    ⟨Distribution.uniform {y : RSA.Residue bits // y.val < max N.val 1 ∧
      y.val.Coprime (max N.val 1)}, Distribution.uniform_isProbDist⟩

/-- Independent uniform units modulo every modulus, for each of `n` indices. -/
def RSA.unitTables (n : ℕ) : Distribution.ProbDist (Fin n → RSA.Residue bits → RSA.Residue bits) :=
  Distribution.ProbDist.pi fun _ => Distribution.ProbDist.pi RSA.unit

/-- The residue modulo `N` of independent uniform residues is uniform. -/
lemma RSA.fTransform_eval_residues (N : RSA.Residue bits) :
    Distribution.fTransform (fun Ys => Ys N) (RSA.residues (bits := bits)).1 =
      (RSA.residue N).1 :=
  Distribution.ProbDist.fTransform_eval_pi RSA.residue N

/-- The units modulo `N` of independent uniform unit tables are independent uniform units. -/
lemma RSA.fTransform_eval_unitTables (n : ℕ) (N : RSA.Residue bits) :
    Distribution.fTransform (fun (rs : Fin n → RSA.Residue bits → RSA.Residue bits) i => rs i N)
        (RSA.unitTables (bits := bits) n).1 =
      Distribution.pi fun _ : Fin n => (RSA.unit N).1 := by
  refine (Distribution.fTransform_pi_map (fun _ : Fin n => (Distribution.ProbDist.pi RSA.unit).1)
    (fun _ r => r N)).trans ?_
  congr 1
  funext i
  exact Distribution.ProbDist.fTransform_eval_pi RSA.unit N

section Units

variable (key : RSA.Key bits)

instance RSA.Key.neZero : NeZero key.N.val := ⟨key.2.ne'⟩

/-- A residue modulo `N` is determined by its class modulo `N`. -/
lemma RSA.eq_iff_cast_eq {x y : RSA.Residue bits} (hx : x.val < key.N.val)
    (hy : y.val < key.N.val) : x = y ↔ (x.val : ZMod key.N.val) = (y.val : ZMod key.N.val) := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Fin.val_inj]

lemma RSA.pow_lt (x : RSA.Residue bits) (n : ℕ) : (key.pow x n).val < key.N.val :=
  Nat.mod_lt _ key.2

lemma RSA.cast_pow (x : RSA.Residue bits) (n : ℕ) :
    ((key.pow x n).val : ZMod key.N.val) = (x.val : ZMod key.N.val) ^ n := by
  change ((x.val ^ n % key.N.val : ℕ) : ZMod key.N.val) = _
  rw [ZMod.natCast_mod, Nat.cast_pow]

lemma RSA.mulMod_val (x y : RSA.Residue bits) :
    (RSA.mulMod key.N x y).val = x.val * y.val % key.N.val :=
  Nat.mod_eq_of_lt ((Nat.mod_lt _ key.2).trans key.N.isLt)

lemma RSA.mulMod_lt (x y : RSA.Residue bits) : (RSA.mulMod key.N x y).val < key.N.val := by
  rw [RSA.mulMod_val]; exact Nat.mod_lt _ key.2

lemma RSA.cast_mulMod (x y : RSA.Residue bits) :
    ((RSA.mulMod key.N x y).val : ZMod key.N.val) =
      (x.val : ZMod key.N.val) * (y.val : ZMod key.N.val) := by
  rw [RSA.mulMod_val, ZMod.natCast_mod, Nat.cast_mul]

lemma RSA.invMod_val (x : RSA.Residue bits) :
    (RSA.invMod key.N x).val = ((x.val : ZMod key.N.val)⁻¹).val :=
  Nat.mod_eq_of_lt ((ZMod.val_lt _).trans key.N.isLt)

lemma RSA.cast_invMod (x : RSA.Residue bits) :
    ((RSA.invMod key.N x).val : ZMod key.N.val) = (x.val : ZMod key.N.val)⁻¹ := by
  rw [RSA.invMod_val, ZMod.natCast_zmod_val]

/-- A unit modulo `N` is a unit of `ℤ/N`. -/
lemma RSA.IsUnit.cast {x : RSA.Residue bits} (hx : RSA.IsUnit key.N x) :
    _root_.IsUnit (x.val : ZMod key.N.val) :=
  (ZMod.isUnit_iff_coprime _ _).mpr hx.2

/-- A residue modulo `N` whose class is a unit is a unit. -/
lemma RSA.isUnit_of_cast {x : RSA.Residue bits} (hx : x.val < key.N.val)
    (hu : _root_.IsUnit (x.val : ZMod key.N.val)) : RSA.IsUnit key.N x :=
  ⟨hx, (ZMod.isUnit_iff_coprime _ _).mp hu⟩

/-- **The challenge `Y · r^e` is a permutation of the units**, for a unit `Y` and a key with
`(x^e)^d ≡ x (mod N)`: it keeps the uniform units. -/
lemma RSA.unit_mul_pow (hkey : ∀ x : RSA.Residue bits, x.val < key.N.val →
      key.pow (key.pow x key.e.val) key.d.val = x)
    {Y : RSA.Residue bits} (hY : RSA.IsUnit key.N Y) :
    Distribution.fTransform (fun r => RSA.mulMod key.N Y (key.pow r key.e.val))
        (RSA.unit key.N).1 = (RSA.unit key.N).1 := by
  have hN : max key.N.val 1 = key.N.val := max_eq_left key.2
  have hp : ∀ r : RSA.Residue bits, r.val < max key.N.val 1 ∧ r.val.Coprime (max key.N.val 1) ↔
      RSA.IsUnit key.N r := fun r => by rw [hN]; rfl
  refine Distribution.fTransform_val_uniform _ (fun r hr => (hp _).mpr ?_)
    fun r s hr hs h => ?_
  · obtain hr := (hp r).mp hr
    refine RSA.isUnit_of_cast key (RSA.mulMod_lt key _ _) ?_
    rw [RSA.cast_mulMod, RSA.cast_pow]
    exact (hY.cast key).mul ((hr.cast key).pow _)
  · have hr' := (hp r).mp hr
    have hs' := (hp s).mp hs
    have hc := congrArg (fun z : RSA.Residue bits => (z.val : ZMod key.N.val)) h
    simp only [RSA.cast_mulMod, RSA.cast_pow] at hc
    have he := (hY.cast key).mul_left_cancel hc
    rw [← RSA.cast_pow, ← RSA.cast_pow] at he
    have := (RSA.eq_iff_cast_eq key (RSA.pow_lt key _ _) (RSA.pow_lt key _ _)).mpr he
    rw [← hkey r hr'.1, ← hkey s hs'.1, this]

/-- **The root of a challenge `Y · r^e`**: for a unit `r`, if `X^e ≡ Y · r^e (mod N)` then
`(X · r⁻¹)^e ≡ Y (mod N)`. -/
lemma RSA.pow_mulMod_invMod {X Y r : RSA.Residue bits} (hY : Y.val < key.N.val)
    (hr : RSA.IsUnit key.N r)
    (h : key.pow X key.e.val = RSA.mulMod key.N Y (key.pow r key.e.val)) :
    key.pow (RSA.mulMod key.N X (RSA.invMod key.N r)) key.e.val = Y := by
  rw [RSA.eq_iff_cast_eq key (RSA.pow_lt key _ _) hY, RSA.cast_pow, RSA.cast_mulMod,
    RSA.cast_invMod, mul_pow, ← RSA.cast_pow, h, RSA.cast_mulMod, RSA.cast_pow, mul_assoc,
    ← mul_pow, ZMod.mul_inv_of_unit _ (hr.cast key), one_pow, mul_one]

/-- There are `N` residues modulo `N`. -/
lemma RSA.card_residues :
    Fintype.card {y : RSA.Residue bits // y.val < max key.N.val 1} = key.N.val := by
  classical
  rw [max_eq_left key.2, Fintype.card_subtype, Fin.card_filter_val_lt]
  exact min_eq_right key.N.isLt.le

/-- There are `φ(N)` units modulo `N`. -/
lemma RSA.card_units :
    Fintype.card {y : RSA.Residue bits // y.val < max key.N.val 1 ∧
      y.val.Coprime (max key.N.val 1)} = Nat.totient key.N.val := by
  classical
  rw [max_eq_left key.2, Fintype.card_subtype, Nat.totient_eq_card_coprime]
  refine Finset.card_bij (fun y _ => y.val) (fun y hy => ?_) (fun y _ y' _ h => Fin.ext h)
    fun a ha => ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hy.1, Nat.coprime_comm.mp hy.2⟩
  · simp only [Finset.mem_filter, Finset.mem_range] at ha
    exact ⟨⟨a, ha.1.trans key.N.isLt⟩, by simpa using ⟨ha.1, Nat.coprime_comm.mp ha.2⟩, rfl⟩

/-- The uniform residue modulo `N`. -/
lemma RSA.residue_apply (y : RSA.Residue bits) :
    (RSA.residue key.N).1 y = if y.val < key.N.val then 1 / (key.N.val : ℝ) else 0 := by
  classical
  change Distribution.fTransform Subtype.val (Distribution.uniform _) y = _
  rw [Distribution.fTransform_val_uniform_apply, RSA.card_residues, max_eq_left key.2]

/-- The uniform unit modulo `N`. -/
lemma RSA.unit_apply (y : RSA.Residue bits) :
    (RSA.unit key.N).1 y =
      if RSA.IsUnit key.N y then 1 / (Nat.totient key.N.val : ℝ) else 0 := by
  classical
  change Distribution.fTransform Subtype.val (Distribution.uniform _) y = _
  rw [Distribution.fTransform_val_uniform_apply, RSA.card_units, max_eq_left key.2]
  rfl

lemma RSA.totient_pos : 0 < Nat.totient key.N.val := Nat.totient_pos.mpr key.2

/-- **A uniform residue is a uniform unit with probability `φ(N)/N`**: pointwise, the uniform
residue is at least `φ(N)/N` times the uniform unit. -/
lemma RSA.unit_le_residue (y : RSA.Residue bits) :
    (Nat.totient key.N.val / key.N.val : ℝ) * (RSA.unit key.N).1 y ≤ (RSA.residue key.N).1 y := by
  rw [RSA.unit_apply, RSA.residue_apply]
  have hφ : (0 : ℝ) < Nat.totient key.N.val := by exact_mod_cast RSA.totient_pos key
  by_cases hu : RSA.IsUnit key.N y
  · rw [if_pos hu, if_pos hu.1, div_mul_div_comm, mul_one, mul_comm, ← div_div,
      div_self hφ.ne']
  · rw [if_neg hu, mul_zero]
    split_ifs <;> positivity

/-- A possible uniform unit modulo `N` is a unit. -/
lemma RSA.isUnit_of_mem_support_unit {y : RSA.Residue bits}
    (hy : y ∈ (RSA.unit key.N).1.support) : RSA.IsUnit key.N y := by
  by_contra h
  exact Finsupp.mem_support_iff.mp hy (by rw [RSA.unit_apply, if_neg h])

/-- **Uniform residues are uniform units with probability `(φ(N)/N)^n`**: pointwise,
independent uniform residues are at least `(φ(N)/N)^n` times independent uniform units. -/
lemma RSA.units_le_residues (n : ℕ) (Z : Fin n → RSA.Residue bits) :
    (Nat.totient key.N.val / key.N.val : ℝ) ^ n *
        Distribution.pi (fun _ => (RSA.unit key.N).1) Z ≤
      Distribution.pi (fun _ : Fin n => (RSA.residue key.N).1) Z := by
  rw [Distribution.pi_apply, Distribution.pi_apply, ← Fin.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun i _ => mul_nonneg (by positivity) ((RSA.unit key.N).2.1 _))
    fun i _ => RSA.unit_le_residue key (Z i)

/-- There are `φ(N)` units modulo `N` among the residues. -/
lemma RSA.card_isUnit :
    (Finset.univ.filter (RSA.IsUnit key.N)).card = Nat.totient key.N.val := by
  classical
  rw [Nat.totient_eq_card_coprime]
  refine Finset.card_bij (fun y _ => y.val) (fun y hy => ?_) (fun y _ y' _ h => Fin.ext h)
    fun a ha => ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hy.1, Nat.coprime_comm.mp hy.2⟩
  · simp only [Finset.mem_filter, Finset.mem_range] at ha
    exact ⟨⟨a, ha.1.trans key.N.isLt⟩, by
      simpa [RSA.IsUnit] using ⟨ha.1, Nat.coprime_comm.mp ha.2⟩, rfl⟩

end Units

end

end Commons
