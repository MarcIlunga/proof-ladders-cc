import ConstructiveCryptography.Functional
import ConstructiveCryptography.InterfaceAlgebra
import ConstructiveCryptography.Notation

/-!
# Distinguishing mixtures

A distinguisher decides on a resource sampled once as on average over its samples: its
probability of outputting `1` on a mixture is the mixture of its probabilities. Two pairs of
sampled resources, the same pair of families of resources sampled once under laws `μ` and `ν`,
are therefore distinguished almost alike: for every `λ ∈ [0, 1]` the advantage on the pair
under `μ` is at most the advantage on the pair under `ν` and `∑ₖ |μ k - λ ν k|`, since each
sample is distinguished with advantage at most one.

Upstream candidates: `Distribution.mass_sum_smul` for `Probability.Distribution`;
`RandomSystem.sLaw_mix`, `RandomSystem.decisionProbability_mix` and
`Domain.Distinguisher.probability_mix` for `RandomSystems.Distance.Distinguisher`; and
`Interface.Resource.behavior_sample`, `Interface.Resource.abs_behavior_sub_le_one`,
`Interface.Resource.advantage_sample_le` and `Interface.Resource.substitutesWithin_sample` for
`ConstructiveCryptography.InterfaceAlgebra`.

## Main results

* `RandomSystem.decisionProbability_mix`, `Domain.Distinguisher.probability_mix`: deciding on a
  mixture is deciding on average
* `Interface.Resource.behavior_sample`: a distinguisher behavior on a sampled resource
* `Interface.Resource.advantage_sample_le`, `Interface.Resource.substitutesWithin_sample`: the
  advantage on a pair of sampled resources under `μ`, from the advantage under `ν`
-/

namespace SystemAlgebra

open Classical Probability

/-- **The mass of a combination of distributions** is the combination of their masses. -/
lemma Distribution.mass_sum_smul {A K : Type*} (s : Finset K) (c : K → ℝ)
    (X : K → Distribution A) (P : A → Prop) :
    (∑ k ∈ s, c k • X k).mass P = ∑ k ∈ s, c k * (X k).mass P := by
  induction s using Finset.induction_on with
  | empty => simp [Distribution.mass]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Distribution.mass_add, ih]
    congr 1
    unfold Distribution.mass
    rw [Finsupp.sum_smul_index (fun _ => by simp), Finsupp.mul_sum]
    exact Finsupp.sum_congr fun a' _ => by split_ifs <;> simp

namespace RandomSystem

variable {A B ι : Type} [Fintype A] [Fintype B] {D : Domain A B}

/-- The transcript law of a mixture is the mixture of the transcript laws. -/
lemma sLaw_mix (P : Distribution.ProbDist ι) (R : ι → RandomSystem A B D)
    (σ : List B →. A) (n : ℕ) :
    (mix P R).sLaw σ n = ∑ i ∈ P.1.support, P.1 i • (R i).sLaw σ n := by
  ext h
  rw [sLaw_apply, Finsupp.finsetSum_apply, mix_mass]
  split_ifs with hg
  · exact Finset.sum_congr rfl fun i _ => by rw [Finsupp.smul_apply, sLaw_apply, if_pos hg]; rfl
  · exact (Finset.sum_eq_zero fun i _ => by
      rw [Finsupp.smul_apply, sLaw_apply, if_neg hg, smul_zero]).symm

end RandomSystem

section Decision

variable {I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {𝒟 : Domain (Σ i, X i) (Σ i, Y i)} {ι : Type}

/-- **A deterministic distinguisher decides on a mixture on average.** -/
lemma RandomSystem.decisionProbability_mix (P : Distribution.ProbDist ι)
    (R : ι → RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟) (D : DDD I X Y) (hD : IsDDD D) :
    (RandomSystem.mix P R).decisionProbability D hD =
      ∑ i ∈ P.1.support, P.1 i * (R i).decisionProbability D hD := by
  unfold RandomSystem.decisionProbability
  rw [RandomSystem.sLaw_mix, Distribution.mass_sum_smul]

/-- **A probabilistic distinguisher decides on a mixture on average.** -/
lemma Domain.Distinguisher.probability_mix (Q : 𝒟.Distinguisher) (P : Distribution.ProbDist ι)
    (R : ι → RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟) :
    Q.probability (RandomSystem.mix P R) = ∑ i ∈ P.1.support, P.1 i * Q.probability (R i) := by
  unfold Domain.Distinguisher.probability
  simp only [RandomSystem.decisionProbability_mix, Finset.mul_sum]
  rw [Finsupp.sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun D _ => by ring

end Decision

namespace Interface.Resource

variable {A : Interface} {K : Type}

/-- **A distinguisher decides on a resource sampled once on average over its samples.** -/
lemma behavior_sample (d : A.inputDomain.DistinguisherBehavior) (P : Distribution K)
    [Distribution.IsProbability P] (R : K → Resource A) :
    d.1 (Resource.sample P R) = ∑ k ∈ P.support, P k * d.1 (R k) := by
  obtain ⟨Q, hQ⟩ := d.2
  rw [show d.1 (Resource.sample P R) = Q.probability (Resource.sample P R).1 from hQ _]
  refine (Q.probability_mix ⟨P, Distribution.IsProbability.isProbDist P⟩ fun k => (R k).1).trans
    (Finset.sum_congr rfl fun k _ => ?_)
  rw [show d.1 (R k) = Q.probability (R k).1 from hQ _]

/-- A distinguisher behavior distinguishes two resources with probability gap at most one. -/
lemma abs_behavior_sub_le_one (d : A.inputDomain.DistinguisherBehavior) (R S : Resource A) :
    |d.1 R - d.1 S| ≤ 1 := by
  have h := (d.advantage_le_transcriptDistance R S).trans
    (RandomSystem.transcriptDistance_le_one R.2 S.2)
  exact (ENNReal.ofReal_le_one).mp h

/-- **Pairs of resources sampled under two laws**: the advantage on the pair `R₁, R₀` sampled
under `μ` is at most the advantage on the pair sampled under `ν` and `∑ₖ |μ k - λ ν k|`, for
every `λ ∈ [0, 1]`. -/
theorem advantage_sample_le [Fintype K] (μ ν : Distribution K) [Distribution.IsProbability μ]
    [Distribution.IsProbability ν] (R₁ R₀ : K → Resource A) {l : ℝ} (hl₀ : 0 ≤ l) (hl₁ : l ≤ 1)
    (d : A.inputDomain.DistinguisherBehavior) :
    d.advantage (Resource.sample μ R₁) (Resource.sample μ R₀) ≤
      d.advantage (Resource.sample ν R₁) (Resource.sample ν R₀) +
        ENNReal.ofReal (∑ k, |μ k - l * ν k|) := by
  -- The gaps of the samples, summed under the two laws.
  set g : K → ℝ := fun k => d.1 (R₁ k) - d.1 (R₀ k)
  have hg : ∀ k, |g k| ≤ 1 := fun k => abs_behavior_sub_le_one d _ _
  have gap : ∀ (P : Distribution K) [Distribution.IsProbability P],
      d.1 (Resource.sample P R₁) - d.1 (Resource.sample P R₀) = ∑ k, P k * g k := by
    intro P _
    rw [behavior_sample, behavior_sample, ← Finset.sum_sub_distrib]
    refine (Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_).trans ?_
    · rw [Finsupp.notMem_support_iff.mp hk]; ring
    · exact Finset.sum_congr rfl fun k _ => by ring
  simp only [Domain.DistinguisherBehavior.advantage]
  rw [gap μ, gap ν, ← ENNReal.ofReal_add (abs_nonneg _)
    (Finset.sum_nonneg fun k _ => abs_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have split : ∑ k, μ k * g k = ∑ k, (μ k - l * ν k) * g k + l * ∑ k, ν k * g k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [split]
  calc |∑ k, (μ k - l * ν k) * g k + l * ∑ k, ν k * g k|
      ≤ ∑ k, |μ k - l * ν k| + |∑ k, ν k * g k| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hg k)
        · rw [abs_mul, abs_of_nonneg hl₀]
          exact mul_le_of_le_one_left (abs_nonneg _) hl₁
    _ = |∑ k, ν k * g k| + ∑ k, |μ k - l * ν k| := add_comm _ _

/-- **A substitution between pairs sampled under another law**: if the pair `R₁, R₀` sampled under
`ν` substitutes within `error`, the pair sampled under `μ` substitutes within `error` and `c`,
for `c` at least `∑ₖ |μ k - λ ν k|` for some `λ ∈ [0, 1]`. -/
theorem substitutesWithin_sample [AdmissibleDistinguishers] [Fintype K] (μ ν : Distribution K)
    [Distribution.IsProbability μ] [Distribution.IsProbability ν] (R₁ R₀ : K → Resource A)
    {error : A.inputDomain.DistinguisherBehavior → ENNReal} {l c : ℝ} (hl₀ : 0 ≤ l) (hl₁ : l ≤ 1)
    (hc : ∑ k, |μ k - l * ν k| ≤ c)
    (h : Resource.sample ν R₁ ≃[error] Resource.sample ν R₀) :
    Resource.sample μ R₁ ≃[fun D => error D + ENNReal.ofReal c] Resource.sample μ R₀ :=
  fun D hD => (advantage_sample_le μ ν R₁ R₀ hl₀ hl₁ D).trans
    (add_le_add (h D hD) (ENNReal.ofReal_le_ofReal hc))

end Interface.Resource

end SystemAlgebra
