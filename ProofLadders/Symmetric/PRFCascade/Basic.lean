import Commons.Definitions.Ideal

/-!
# PRF cascade

The second problem of the symmetric ladder [1, §2]: if `F : K → X → X` is a secure PRF on a
finite set `X`, with keys in a finite set `K`, then the cascade

$$H(k_1 \,\|\, k_2, x) = F(k_2, F(k_1, x))$$

is a secure PRF on `X`, with keys in `K × K`. The notes' input and output length `λ`, keys,
inputs and outputs in `{0,1}^λ`, is the instance `K = X = Bits λ`.

This module holds what the proofs share: the cascade, its interface, and the composition
`T₂ ∘ T₁` of two independent uniform random functions, the cascade once both keyed functions are
ideal. The code-based proof (`CodeBased`) reaches `T₂ ∘ T₁` by the notes' hybrids; the pure-systems
statements (`PureSystems`) bound its distance to the uniform random function; the bonus `k₁ = k₂`
(`Bonus`) uses both.

```
          x
    D ─────────► ┌──────────────────┐
      ◄───────── │ T₁, T₂ ← X → X   │   composedURF X
       T₂(T₁ x)  └──────────────────┘
```

## Main definitions

* `H F`: the cascade
* `Queries X q`: its interface, inputs and outputs in `X`, at most `q` queries
* `composedURF X`: the composition `T₂ ∘ T₁` of two independent uniform random functions

## References

1. The symmetric proof ladder, *Security proofs in the style of The Joy of Cryptography*,
   `proof-ladders/symmetric-ladder`, `Notes/selfcontained.tex`.
-/

namespace ProofLadders.PRFCascade

open Commons Probability SystemAlgebra SystemAlgebra.Interface

/-- **The cascade** `H(k₁ ‖ k₂, x) = F(k₂, F(k₁, x))`. -/
def H {K X : Type} (F : K → X → X) (key : K × K) (x : X) : X :=
  F key.2 (F key.1 x)

noncomputable section

variable (X : Type) [Fintype X] [DecidableEq X] [Nonempty X]

/-- The interface of the cascade: inputs and outputs in `X`, at most `q` queries. -/
abbrev Queries (q : Evaluation.Port → ℕ) : Interface :=
  Evaluation.perPort X X q

/-- **The composition `T₂ ∘ T₁`** of two independent uniform random functions. -/
def composedURF {q : Evaluation.Port → ℕ} : Resource (Queries X q) :=
  Resource.sample (Distribution.uniform ((X → X) × (X → X)))
    fun T => Resource.ofFunction fun _ x => T.2 (T.1 x)

end

end ProofLadders.PRFCascade
