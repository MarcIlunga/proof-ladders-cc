import RandomSystems.Distance.Decision
import Probability.StatisticalDistance

/-!
# The H-coefficient technique

Two random systems `R` and `S` on the same domain are close when, outside a set of bad
transcripts, every transcript is almost as probable for `R` as for `S`. If `R(h) ≥ (1 - ε) S(h)`
for every transcript `h` that is not bad, and under every compatible query-bounded strategy the
transcript of `S` is bad with probability at most `δ`, then the transcript distance of `R` and
`S` is at most `ε + δ`. Under a fixed strategy, the transcript law of a system gives each
transcript the strategy produces its probability for the system, and every other transcript
`0`; the ratio therefore passes to the two transcript laws, whose statistical distance is then
at most `ε` plus the probability of bad under the law of `S`.

Upstream candidate (trailofbits/constructive-cryptography, systems level):
`RandomSystem.transcriptDistance_le_of_ratio`, for `RandomSystems.Distance.Decision`.

## Main results

* `RandomSystem.transcriptDistance_le_of_ratio`: the H-coefficient bound on the transcript
  distance

## References

1. J. Patarin. *The "Coefficients H" Technique*. Selected Areas in Cryptography, SAC 2008,
   pp. 328–345. Springer, 2009.
-/

namespace SystemAlgebra.RandomSystem

open Probability

variable {I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {𝒟 : Domain (Σ i, X i) (Σ i, Y i)}

/-- **The H-coefficient bound** [1]: if every transcript `h` that is not bad has
`R(h) ≥ (1 - ε) S(h)`, and every compatible strategy with at most `n` queries makes the
transcript of `S` bad with probability at most `δ`, then `R` and `S` are within `ε + δ`. -/
lemma transcriptDistance_le_of_ratio {R S : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟}
    (hR : R.RepliesAtQueriedInterface) (hS : S.RepliesAtQueriedInterface)
    (Bad : List ((Σ i, X i) × (Σ i, Y i)) → Prop) {ε δ : ℝ} (hε : 0 ≤ ε)
    (ratio : ∀ h, ¬ Bad h → (1 - ε) * S h ≤ R h)
    (bad : ∀ (E : DDE (Σ i, X i) (Σ i, Y i)) (n : ℕ), QueryBounded n E → 𝒟.Compatible E →
      probBad (S.sLaw E.1 n) Bad ≤ δ) :
    R.transcriptDistance S ≤ ENNReal.ofReal (ε + δ) := by
  -- The transcript distance is the largest statistical distance of the transcript laws under a
  -- query-bounded strategy `E`, compatible with the domain, within `n` rounds: bound each one.
  refine iSup_le fun E => iSup_le fun n => iSup_le fun hn => iSup_le fun hc => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  -- Both transcript laws are probability distributions, since `E` is compatible with both
  -- systems.
  have lawR := R.sLaw_isProbDist (hc R hR) n
  have lawS := S.sLaw_isProbDist (hc S hS) n
  -- The ratio passes to the transcript laws.
  have lawRatio : ∀ h, ¬ Bad h → (1 - ε) * S.sLaw E.1 n h ≤ R.sLaw E.1 n h := by
    intro h notBad
    -- Each law is the system's probability of `h` if `E` produces `h` within `n` rounds, and
    -- `0` otherwise.
    rw [sLaw_apply, sLaw_apply]
    split_ifs
    · -- `E` produces `h`: the ratio of the two systems.
      exact ratio h notBad
    · -- `E` does not produce `h`: `(1 - ε) · 0 ≤ 0`.
      simp
  -- The statistical distance of two probability distributions with this ratio outside `Bad`
  -- is at most the probability of `Bad` under the second, plus `ε`. Its arguments: the two
  -- laws, the bad set, `ε` as a non-negative real, the non-negativity of both laws, their
  -- equal weights `1 = 1`, the weight `1 ≤ 1` of the second, and the ratio.
  have distance := statDist_le_probBad_add_of_ratio_on_good (R.sLaw E.1 n) (S.sLaw E.1 n) Bad
    ⟨ε, hε⟩ lawR.1 lawS.1 (lawR.2.trans lawS.2.symm) lawS.2.le lawRatio
  -- The non-negative real `ε` is `ε`.
  change _ ≤ _ + ε at distance
  -- Under `E`, the transcript of `S` is bad with probability at most `δ`.
  have badBound := bad E n hn hc
  linarith
