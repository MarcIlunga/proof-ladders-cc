import ConstructiveCryptography.Substitution.Reduction
import Mathlib.Algebra.BigOperators.Fin

/-!
# The hybrid argument for substitutions within error functions

The hybrid argument of Banfi [1, Lemma 2.3.2] for substitutions within distinguisher-indexed
error functions: hybrids `H 0, …, H n`, each substituting for the next within its error, give a
substitution of the first for the last within the sum of the errors. The library has it for
substitution relations (`SubstitutionRelation.substitutes_of_hybrid`) and for distances
(`SubstitutionRelation.distance_hybrid_le`).

A substitution within an error also holds within any larger error.

Upstream candidates: `DistinguisherAdvantage.SubstitutesWithin.hybrid` and
`DistinguisherAdvantage.SubstitutesWithin.mono` for
`ConstructiveCryptography.Substitution.Reduction`, beside `SubstitutesWithin.trans`.

## Main results

* `DistinguisherAdvantage.SubstitutesWithin.hybrid`: the hybrid argument
* `DistinguisherAdvantage.SubstitutesWithin.mono`: a larger error

## References

1. F. Banfi. *A Composable Treatment of Anonymous Communication*. Doctoral thesis, ETH Zurich,
   2023.
-/

namespace ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage

variable {C : Type*} {Systems : C → Type*} {Distinguisher : C → Type*}

/-- **The hybrid argument** [1, Lemma 2.3.2]: if each hybrid `H i` substitutes for the next
within `error i`, the first hybrid substitutes for the last within the sum of the errors. -/
theorem SubstitutesWithin.hybrid (model : DistinguisherAdvantage C Systems Distinguisher)
    {A : C} {n : ℕ} (H : Fin (n + 1) → Systems A) (error : Fin n → Distinguisher A → ENNReal)
    (step : ∀ i : Fin n, model.SubstitutesWithin (error i) (H i.castSucc) (H i.succ)) :
    model.SubstitutesWithin (fun D => ∑ i, error i D) (H 0) (H (Fin.last n)) := by
  induction n with
  | zero =>
    intro D _
    rw [show Fin.last 0 = 0 from rfl, model.advantage_self]
    exact zero_le
  | succ n ih =>
    have chain := SubstitutesWithin.trans model
      (ih (fun i => H i.castSucc) (fun i => error i.castSucc) fun i => step i.castSucc)
      (step (Fin.last n))
    intro D hD
    refine (chain D hD).trans (le_of_eq ?_)
    exact (Fin.sum_univ_castSucc fun i => error i D).symm

/-- **A larger error**: a substitution within `error` holds within every error at least `error` at
the admitted distinguishers. -/
lemma SubstitutesWithin.mono (model : DistinguisherAdvantage C Systems Distinguisher) {A : C}
    {error error' : Distinguisher A → ENNReal} {left right : Systems A}
    (substitution : model.SubstitutesWithin error left right)
    (le : ∀ D ∈ model.admissible A, error D ≤ error' D) :
    model.SubstitutesWithin error' left right :=
  fun D hD => (substitution D hD).trans (le D hD)

end ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage
