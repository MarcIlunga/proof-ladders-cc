import ProofLadders.Symmetric.PRFCascade.PureSystems
import ProofLadders.Common.Symmetric
import ProofLadders.Common.Functional
import ConstructiveCryptography.DSL
import ConstructiveCryptography.Tactics.Substitution

/-!
# PRF cascade: the bonus

The bonus of [1, §2]: with the key schedule `k₁ = k₂`, the cascade `F(k, F(k, x))` is still a
secure PRF, with the collision bound `q(3q-1)/(2|X|)`; at `X = Bits λ` it is `q(3q-1)/2^{λ+1}`.
The notes give no proof of it, and this proof mixes the two styles. The PRF step is a
substitution through the DSL calling program `𝓢`, which queries `F(k, ·)` twice per query, as in
the code-based proof; the collision step is the pure-systems bound on `T ∘ T`
(`PureSystems.selfComposedURF_distance_le`).

```
  prf-real^{sameKey F}
  = 𝓢 • prf-real^F      F(k, F(k, x)) by two calls
  ≃ 𝓢 • prf-rand^F      PRF security of F, at the inside budget 2q
  = T ∘ T               the uniform random function inlined
  ≈ prf-rand            pure systems: within q(3q-1)/(2|X|)
```

## Main definitions

* `sameKey F`: the cascade with one key, `F(k, F(k, x))`
* `𝓢 X`, `𝓢.perPortBound X q`: the calling program of the PRF step, at per-port budgets

## Main results

* `𝓢_smul_ofFunction`, `𝓢_smul_prfReal`, `𝓢_smul_urf`: `𝓢` on a function `g` is `g ∘ g`, on
  `prf-real^F` the cascade with one key, on the uniform random function `T ∘ T`
* `prf_cascade_same_key`, `prf_cascade_same_key_bits`: the cascade with one key is a secure PRF

## References

1. The symmetric proof ladder, *Security proofs in the style of The Joy of Cryptography*,
   `proof-ladders/symmetric-ladder`, `Notes/selfcontained.tex`.
-/

namespace ProofLadders.PRFCascade.Bonus

open Commons Probability SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface
open scoped SystemAlgebra SystemAlgebra.DSL

/-- **The cascade with the key schedule `k₁ = k₂`**: `F(k, F(k, x))`. -/
def sameKey {K X : Type} (F : K → X → X) (k : K) (x : X) : X :=
  F k (F k x)

-- `𝓢`: on `x`, `y ← prf.query(x)` and return `prf.query(y)`.
converter 𝓢(X : Type) [Fintype X] : Evaluation X X
  inside prf : Evaluation X X
  on eval(x : X) → X
    y ← prf.eval(x)
    z ← prf.eval(y)
    return z

noncomputable section

variable {K X : Type} [Fintype K] [Nonempty K] [Fintype X]

variable (X) in
/-- **`𝓢` at per-port budgets**: `q` queries make at most `𝓢.bound = 2` calls each. -/
def 𝓢.perPortBound (q : Evaluation.Port → ℕ) :
    Queries X q ⟶ Queries X (fun _ => 𝓢.bound X * q .eval) :=
  Interface.Converter.ofProgramPerPort none (𝓢.body X) (𝓢.bound_spec X) q (q .eval)
    (Fintype.sum_unique q).le

/-- **`𝓢` on a function** `g` is `g ∘ g`. -/
lemma 𝓢_smul_ofFunction (q : Evaluation.Port → ℕ) (g : X → X) :
    𝓢.perPortBound X q • Resource.ofFunction (fun _ => g) =
      Resource.ofFunction (A := Queries X q) fun _ x => g (g x) := by
  -- `𝓢` is the converter of its program; on a function it is the function computed by one
  -- invocation against it.
  unfold 𝓢.perPortBound Interface.Converter.ofProgramPerPort Interface.Converter.ofProgram
  refine Interface.ofDDC_ofProgramOn_smul_ofFunction (A := Queries X q)
    (B := Queries X (fun _ => 𝓢.bound X * q .eval))
    none (𝓢.body X) (𝓢.bound_spec X) _ (fun _ => g) _ fun t o x => ?_
  -- Against `g`, an invocation makes its two calls, `prf(x) ⇒ g x` and `prf(g x) ⇒ g (g x)`,
  -- and returns `g(g(x))`, from either state.
  cases o
  refine ⟨some (), ?_⟩
  cases t <;> simp [Program.answer, 𝓢.body, callProg, returnProg]

/-- **`𝓢` on `prf-real^F`** is the cascade with one key. -/
lemma 𝓢_smul_prfReal (F : K → X → X) (q : Evaluation.Port → ℕ) :
    𝓢.perPortBound X q • PRF.Real F = PRF.Real (sameKey F) := by
  -- `prf-real^F` samples a key `k` and is the function `F(k, ·)`; `𝓢` attaches to each sample, ...
  unfold PRF.Real
  rw [Resource.smul_sample]
  congr 1
  funext k
  -- ... where it is `F(k, F(k, ·))`.
  exact 𝓢_smul_ofFunction q (F k)

variable [DecidableEq X] [Nonempty X]

variable (X) in
/-- **`𝓢` on the uniform random function** is `T ∘ T`. -/
lemma 𝓢_smul_urf (q : Evaluation.Port → ℕ) :
    𝓢.perPortBound X q • URF (Queries X (fun _ => 𝓢.bound X * q .eval)) =
      PureSystems.selfComposedURF X := by
  -- The uniform random function samples `T` once; `𝓢` attaches to each sample, ...
  rw [URF_perPort_eq, Resource.smul_sample]
  congr 1
  funext T
  -- ... where it is `T(T(·))`.
  exact 𝓢_smul_ofFunction q T

/-- **The bonus of [1, §2]**: with `k₁ = k₂` the cascade is still a secure PRF, with the collision
bound `q(3q-1)/(2|X|)`. The notes give no proof: the PRF step is a substitution through `𝓢`,
which queries `F(k, ·)` twice per query, at the inside budget `2q`, and the collision step is the
pure-systems bound on `T ∘ T` (`PureSystems.selfComposedURF_distance_le`). -/
theorem prf_cascade_same_key [AdmissibleDistinguishers] (F : K → X → X) (q : Evaluation.Port → ℕ)
    (ε : (Queries X (fun _ => 𝓢.bound X * q .eval)).inputDomain.DistinguisherBehavior → ENNReal)
    (secure : PRF.Secure F ε) :
    PRF.Secure (sameKey F) fun D => ε (absorb (𝓢.perPortBound X q) D) +
      ENNReal.ofReal ((q .eval : ℝ) * (3 * (q .eval : ℝ) - 1) / (2 * Fintype.card X)) := by
  --   D ─ prf-real^{sameKey F}                      start
  --   D ─ 𝓢 ─ prf-real^F     =                      F(k, F(k, x)) by two calls   𝓢_smul_prfReal
  --   D ─ 𝓢 ─ prf-rand^F     ≃[ε(D ∘ 𝓢)]            PRF security of F
  --   D ─ T ∘ T              =                      inline the uniform function  𝓢_smul_urf
  --   D ─ prf-rand           ≈[q(3q-1)/(2|X|)]      pure systems                 selfComposedURF_…
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    -- factor out both calls of `F(k, ·)` into `prf-real^F`, with the calling program `𝓢`
    PRF.Real (sameKey F) = 𝓢.perPortBound X q • PRF.Real F := (𝓢_smul_prfReal F q).symm
    -- swap `prf-real^F` for the uniform random function inside `𝓢`: the PRF assumption at `D ∘ 𝓢`
    _ ≃[fun D => ε (absorb (𝓢.perPortBound X q) D)]
        𝓢.perPortBound X q • URF (Queries X (fun _ => 𝓢.bound X * q .eval)) :=
      AdmissibleDistinguishers.substitutesWithin_attach _ secure
    -- inline the uniform random function: `T ∘ T`
    _ = PureSystems.selfComposedURF X := 𝓢_smul_urf X q
    -- the collision step, a pure-systems bound
    _ ≈[ENNReal.ofReal ((q .eval : ℝ) * (3 * (q .eval : ℝ) - 1) / (2 * Fintype.card X))]
        URF (Queries X q) := PureSystems.selfComposedURF_distance_le X q

/-- **The bonus of [1, §2] at `{0,1}^λ`**, the notes' setting: with `k₁ = k₂` and `F` with keys,
inputs and outputs in `{0,1}^λ`, the collision bound is `q(3q-1)/2^{λ+1}`. The security
parameter `λ` is `secpar`. -/
theorem prf_cascade_same_key_bits [AdmissibleDistinguishers] {secpar : ℕ}
    (F : Bits secpar → Bits secpar → Bits secpar) (q : Evaluation.Port → ℕ)
    (ε : (Queries (Bits secpar)
      (fun _ => 𝓢.bound (Bits secpar) * q .eval)).inputDomain.DistinguisherBehavior → ENNReal)
    (secure : PRF.Secure F ε) :
    PRF.Secure (sameKey F) fun D => ε (absorb (𝓢.perPortBound (Bits secpar) q) D) +
      ENNReal.ofReal ((q .eval : ℝ) * (3 * (q .eval : ℝ) - 1) / 2 ^ (secpar + 1)) := by
  -- `|{0,1}^λ| = 2^λ`, and `2 · 2^λ = 2^{λ+1}`.
  simpa only [card_bits, Nat.cast_pow, Nat.cast_ofNat, ← pow_succ'] using
    prf_cascade_same_key F q ε secure

end

end ProofLadders.PRFCascade.Bonus
