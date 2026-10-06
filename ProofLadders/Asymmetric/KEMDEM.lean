import ProofLadders.Common.PublicKey
import ProofLadders.Common.ProbAutomaton
import ProofLadders.Common.Mixtures
import ConstructiveCryptography.Tactics.Substitution

/-!
# KEM + DEM

The problem of the asymmetric ladder [1]: a KEM and a DEM whose key spaces match give a PKE
(Figure 2). Theorem 1 of [1]: if the KEM is perfectly correct, the advantage of an adversary
against the single-challenge CCA security of the PKE is at most the sum of the advantages of the
adversaries `B₁⁰` and `B₁¹` against the KEM and `B₂` against the DEM (Figure 4). Each notion is
a converter on the real system of its scheme (`Common/PublicKey`, `Common/Encryption`): the
challenge for the bit `b` on the public key, `E_pk` and `D_sk` of the PKE or of the KEM, and on
`⟦E_k, D_k⟧` of the DEM for a uniform key. The games of Figure 1 are the systems
`PKE.ChallengeCCA.Game`, `KEM.ChallengeCCA.Game` and `DEM.ChallengeCCA.Game`, each the challenge
on its real system (`…Game.eq_real`). The adversaries are converters: `B₁ b` runs the PKE game
for the bit `b` on the input `(pk, c₁*, k*)` of the KEM game, and `B₂` runs it with its own KEM
keys on the challenge of the DEM game. An adversary against the KEM or the DEM is a distinguisher
reduced through them.

Two of the variants of [1, §3.1] are stated:

* imperfect correctness: the first step of the proof is up to the bad event that decapsulating
  `c₁*` misses `k*`, which costs the correctness error `δ` for each value of the bit;
* the CPA variant, in the many-challenge form of [2, 3]: KEM IND-CPA (`KEM.INDCPA` of Commons)
  and one-time DEM security give left-or-right CPA security of the PKE, through the reductions
  `R1(E)` and `R3(E)` to the KEM, which encrypt the left and the right message under the key of
  each KEM encapsulation, and `R2(K)` (`𝓡ₒ`) to the DEM, which encapsulates itself. The libraries
  `Left` and `Right` of `CPA` and of `OTS` of [2] are `Left` and `Right` on the public key and
  `E_pk` of the PKE, and on the one-time encryption system of the DEM (`…eq_real`).

The random-oracle variant is not stated.

Style: pure random systems. The games of [1] are systems, and the sequence of games of Figure 3
is a chain of equalities and substitutions through the converters `B₁ b` and `B₂`, from the
challenge for the bit `0` on the real PKE to the one for the bit `1`:
`IND-CCA^PKE(0) = G₁(0) = B₁ 0 • IND-CCA^KEM(0) ≃ B₁ 0 • IND-CCA^KEM(1) = G₂(0) =
B₂ • IND-CCA^DEM(0) ≃ B₂ • IND-CCA^DEM(1) = G₂(1) = B₁ 1 • IND-CCA^KEM(1) ≃ B₁ 1 • IND-CCA^KEM(0)
= G₁(1) = IND-CCA^PKE(1)`, where each game of Figure 1 enters as its challenge on the real
system, and each substitution is that of the challenges. The bad event of the
imperfect-correctness variant is independent of the adversary, so its first step is a
statistical one, `IND-CCA^PKE(b) ≈[δ] G₁(b)`. The CPA variant is the chain of [2, 3]:
`Left = R1(E) • KEM-real ≃ R1(E) • KEM-ideal = R2(K) • OTS-Left ≃ R2(K) • OTS-Right =
R3(E) • KEM-ideal ≃ R3(E) • KEM-real = Right`, with the libraries as their converters on the real
systems.

The equalities are simulations of the fresh-sampling automata of the games: `B₁ b` on the real
KEM game is `G₁(b)` along the map of states that forgets `k₁`, and on the ideal one `G₂(b)` along
the map that reads `k* = k₁`; `B₂` on the DEM game simulates `G₂(b)` along the kernel that samples
`k*` while the DEM game is uninitialized; `IND-CCA^PKE(b)` simulates `G₁(b)` along the kernel that
samples the encapsulations, given the challenge one once there is a challenge, which a perfectly
correct KEM decapsulates to the encapsulated key. Without perfect correctness, `IND-CCA^PKE(b)`
and `G₁(b)` are mixtures over the keys and the encapsulations sampled once, which agree on the
samples under which decapsulating `c₁*` gives `k*`. In the CPA variant, `R1(E)` on the real KEM
is `Left` along the map of states that keeps the keys, and on the ideal KEM `R2(K)` on
`OTS-Left` along the map that forgets the table of the ideal KEM. Each game or library of the
sources is its converter on the real system along the map of states that keeps the keys and the
challenge: the real system samples the keys at its first query, and the KEM challenge
encapsulates at the first query, so that its state is the input `(pk, c*, k_b)`.

Upstream candidates: `KEM.encapsulationsGiven`, `KEM.bindK_encapsulations`,
`SymmetricEncryption.bindK_encryptions`, `PublicKeyEncryption.bindK_encryptions`, the games and
libraries of the sources with their presentations `…eq_real`, and the fresh-sampling
presentations and steps of `IND-CCA^PKE`, `IND-CCA^KEM`, `IND-CCA^DEM`, `Left`, `Right`,
`KEM-real`, `KEM.CCA`, `OTS-Left`, `OTS-Right`, of the real systems `AE.Real`, `PKE.Real` and
`Encryption.OneTime`, and of the converters of the notions on them, for `Common/PublicKey` and
`Common/Encryption`; `ProbStep.belief_bindK` and `Interface.Resource.ofProbAutomaton_fTransform`
for `Common/ProbAutomaton`; `statDist_add_right` and `Interface.Resource.distance_sample_le` for
`Common/Mixtures`.

## Main definitions

* `PKE.ChallengeCCA.Game pke b`, `KEM.ChallengeCCA.Game kem b`, `DEM.ChallengeCCA.Game dem b`:
  the games `IND-CCA^PKE(b)`, `IND-CCA^KEM(b)` and `IND-CCA^DEM(b)` of Figure 1
* `PKE.LORCPA.Left pke`, `PKE.LORCPA.Right pke`, `Encryption.OTSLeft dem`,
  `Encryption.OTSRight dem`: the libraries `Left` and `Right` of `CPA` and of `OTS` of [2]
* `scheme kem dem`: the KEM+DEM construction
* `G₁ kem dem b`, `G₂ kem dem b`: the games of Figure 3
* `B₁ dem b`, `B₂ kem dem`: the adversaries of Figure 4
* `R1 dem`, `𝓡ₒ kem`, `R3 dem`: the reductions `R1(E)`, `R2(K)` and `R3(E)` of [2, 3]
* `kemBudget q`, `R1.perLabel`, `R3.perLabel`: the KEM budget of `R1(E)` and `R3(E)`, and the
  reductions at per-label inside budgets
* `G₁.freshSampling`, `G₂.freshSampling`, `PKE.ChallengeCCA.Game.freshSampling`,
  `KEM.ChallengeCCA.Game.freshSampling`, `DEM.ChallengeCCA.Game.freshSampling`,
  `B₁.freshSamplingKEM`, `B₂.freshSamplingDEM`: the games, and the adversaries on their games, as
  fresh sampling
* `DEM.ChallengeCCA.Challenge.freshSamplingReal`, `PKE.ChallengeCCA.Challenge.freshSamplingReal`,
  `KEM.ChallengeCCA.Challenge.freshSamplingReal`: the challenges on the real systems as fresh
  sampling
* `PKE.LORCPA.Left.freshSampling`, `PKE.LORCPA.Right.freshSampling`, `KEM.Real.freshSampling`,
  `KEM.CCA.freshSampling`, `R1.freshSampling`, `R3.freshSampling`, `𝓡ₒ.freshSampling`,
  `Encryption.OTSLeft.freshSampling`, `Encryption.OTSRight.freshSampling`: the systems of the CPA
  variant, and the reductions on them, as fresh sampling
* `PKE.Left.freshSamplingReal`, `PKE.Right.freshSamplingReal`,
  `Encryption.Left.freshSamplingOneTime`, `Encryption.Right.freshSamplingOneTime`: `Left` and
  `Right` on the real PKE and on the one-time encryption system as fresh sampling
* `B₁.stateG₁`, `B₁.stateG₂`: the states of `G₁(b)` and `G₂(b)` of a state of `B₁ b` on the KEM
  game
* `B₂.kernelG₂`, `PKE.ChallengeCCA.Game.kernelG₁`: the states of `G₂(b)` of a state of `B₂` on the
  DEM game, and of `G₁(b)` of a state of `IND-CCA^PKE(b)`, sampling what is not yet sampled
* `PKE.ChallengeCCA.Game.upfrontStep`: `IND-CCA^PKE(b)` with the challenge encapsulation upfront
* `PKE.ChallengeCCA.Game.kernelUpfront`, `G₁.stateUpfront`: its states of a state of
  `IND-CCA^PKE(b)` and of `G₁(b)`
* `state𝓡ₒ`: the state of `R2(K) • OTS` of a state of `R1(E)` or `R3(E)` on the ideal KEM

## Main results

* `G₁.outcome_*`, `G₂.outcome_*`, `PKE.ChallengeCCA.Game.outcome_*`,
  `KEM.ChallengeCCA.Game.outcome_*`, `DEM.ChallengeCCA.Game.outcome_*`, `B₁.outcome_*`,
  `B₂.outcome_*`: the games and the adversaries as steps
* `AE.Real.outcome_*`, `PKE.Real.outcome_*`, `KEM.Real.outcome_*`,
  `Encryption.OneTime.outcome_enc`, `DEM.ChallengeCCA.Challenge.outcome_*`,
  `PKE.ChallengeCCA.Challenge.outcome_*`, `KEM.ChallengeCCA.Challenge.outcome_*`,
  `PKE.Left.outcome_*`, `PKE.Right.outcome_*`, `Encryption.Left.outcome_enc`,
  `Encryption.Right.outcome_enc`: the real systems and the converters of the notions as steps
* `DEM.ChallengeCCA.Game.eq_real`, `PKE.ChallengeCCA.Game.eq_real`,
  `KEM.ChallengeCCA.Game.eq_real`: each game of Figure 1 is the challenge on its real system
* `PKE.LORCPA.Left.eq_real`, `PKE.LORCPA.Right.eq_real`, `Encryption.OTSLeft.eq_real`,
  `Encryption.OTSRight.eq_real`: the libraries of [2] are `Left` and `Right` on the real systems
* `game_eq_G₁`, `game_G₁_distance_le`, `G₁_eq_B₁`, `G₂_eq_B₁`, `G₂_eq_B₂`: the steps of Figure 3
* `PKE.ChallengeCCA.Game.eq_sample`, `G₁.eq_sample`, `G₁.eq_upfront`: `IND-CCA^PKE(b)` and
  `G₁(b)` as mixtures over the upfront sample, which agree on a good sample
* `G₁_substitutes`: the KEM and DEM swaps, `G₁(0) ≃ G₁(1)`
* `kem_dem_cca`: Theorem 1 of [1]
* `kem_dem_cca_of_correctnessError`: the imperfect-correctness variant
* `left_eq_R1`, `R1_eq_𝓡ₒ`, `R3_eq_𝓡ₒ`, `right_eq_R3`: the steps of the CPA variant
* `kem_dem_cpa`: the CPA variant

## References

1. M. Barbosa. *Yet another set of HACS examples*. The asymmetric proof ladder,
   `proof-ladders/asymmetric-ladder`, `asymmetric-problems.pdf`, 2025.
2. The asymmetric proof ladder, KEM-DEM in ProofFrog, `kemdem/ProofFrog/src`: `PKE-CPA.game`,
   `SymEnc-OTS.game` and `Hyb-is-CPA.proof`.
3. The asymmetric proof ladder, KEM-DEM in EasyCrypt,
   `kemdem/EasyCrypt/multi-challenge/KEMDEM_CPA.ec`.
-/

namespace ProofLadders.KEMDEM

open Commons Probability SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface
open ConstructiveCryptography.CryptographicAlgebra
open scoped SystemAlgebra SystemAlgebra.DSL
open Probability.Distribution

noncomputable section

/-! ## Upstream candidates

Mixtures of probabilistic automata and the distance of mixtures: an automaton started from a law
is the mixture of the automaton started at its points, and two resources sampled once under the
same law are at distance at most the mass of the samples on which they differ. -/

section UpstreamCandidates

/-- **The forward algorithm is linear in the initial law.** -/
lemma ProbStep.belief_bindK {S I : Type} {X Y : I → Type} (step : ProbStep S I X Y)
    (D : Domain (Σ i, X i) (Σ i, Y i)) {Z : Type} (μ : Distribution Z) (f : Z → Distribution S)
    (h : List ((Σ i, X i) × (Σ i, Y i))) :
    step.belief D (bindK μ f) h = bindK μ fun z => step.belief D (f z) h := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h e ih =>
    obtain ⟨x, y⟩ := e
    simp only [ProbStep.belief_snoc]
    by_cases hd : D h x
    · simp only [hd, if_true, ih, ProbStep.transition, bindK_bindK]
    · simp only [hd, if_false, bindK_zero_right]

/-- **A probabilistic automaton started from the image of a law** is the mixture, over the law,
of the automaton started at each point. -/
lemma Interface.Resource.ofProbAutomaton_fTransform {T : Interface} {S Z : Type}
    (step : ProbStep S T.I T.X T.Y) (μ : Distribution.ProbDist Z) (init : Z → S) :
    Interface.Resource.ofProbAutomaton T step ⟨fTransform init μ.1, fTransform_isProbDist _ μ.2⟩ =
      Interface.Resource.sample μ.1 fun z =>
        Interface.Resource.ofProbAutomaton T step (Distribution.ProbDist.single (init z)) := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [Interface.Resource.sample_mass]
  change (step.belief _ (fTransform init μ.1) h).weight =
    ∑ z ∈ μ.1.support, μ.1 z * (step.belief _ (Finsupp.single (init z) 1) h).weight
  rw [fTransform_eq_bindK, ProbStep.belief_bindK, weight_bindK]
  rfl

/-- The statistical distance is unchanged by adding a distribution to both sides. -/
lemma statDist_add_right {A : Type*} (X Y W : Distribution A) :
    statDist (X + W) (Y + W) = statDist X Y := by
  unfold statDist
  rw [show X + W - (Y + W) = X - Y by abel]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Finsupp.coe_add, Pi.add_apply, add_sub_add_right_eq_sub]

/-- **Two resources sampled once under the same law** are at distance at most the mass of the
samples on which they differ. -/
lemma Interface.Resource.distance_sample_le {A : Interface} {K : Type} (μ : Distribution K)
    [Distribution.IsProbability μ] (R S : K → Resource A) (bad : K → Prop)
    (h : ∀ k ∈ μ.support, ¬ bad k → R k = S k) :
    Δ (Resource.sample μ R) (Resource.sample μ S) ≤ ENNReal.ofReal (μ.mass bad) := by
  classical
  rw [Interface.cc_distance_eq]
  refine iSup_le fun E => iSup_le fun n => iSup_le fun _ => iSup_le fun hc =>
    ENNReal.ofReal_le_ofReal ?_
  have hμ := (Distribution.IsProbability.isProbDist μ).1
  change statDist ((RandomSystem.mix ⟨μ, _⟩ fun k => (R k).1).sLaw E.1 n)
    ((RandomSystem.mix ⟨μ, _⟩ fun k => (S k).1).sLaw E.1 n) ≤ _
  rw [RandomSystem.sLaw_mix, RandomSystem.sLaw_mix]
  dsimp only
  -- The good samples contribute alike, and each bad one at most its mass.
  have hgood : ∑ k ∈ μ.support with ¬ bad k, μ k • (R k).1.sLaw E.1 n =
      ∑ k ∈ μ.support with ¬ bad k, μ k • (S k).1.sLaw E.1 n :=
    Finset.sum_congr rfl fun k hk => by
      rw [h k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2]
  rw [← Finset.sum_filter_add_sum_filter_not μ.support bad
      (fun k => μ k • (R k).1.sLaw E.1 n),
    ← Finset.sum_filter_add_sum_filter_not μ.support bad (fun k => μ k • (S k).1.sLaw E.1 n),
    hgood, statDist_add_right]
  refine (statDist_le_weight (fun a => ?_) (fun a => ?_)).trans (le_of_eq ?_)
  · rw [Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hμ k) (RandomSystem.sLaw_nonNeg _ a)
  · rw [Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hμ k) (RandomSystem.sLaw_nonNeg _ a)
  · rw [← mass_true, Distribution.mass_sum_smul, Finset.sum_filter, Distribution.mass,
      Finsupp.sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · rw [mass_true, ((R k).1.sLaw_isProbDist (hc _ (R k).2) n).2, mul_one]
    · rfl

end UpstreamCandidates

variable {PK SK C₁ K M C₂ : Type} [Fintype PK] [Fintype SK] [Fintype C₁] [Fintype K] [Fintype M]
  [Fintype C₂]

/-! ## The games of the sources

The games of [1, Figure 1], and the libraries `Left` and `Right` of `CPA` and of `OTS` of [2].
Each is the converter of its notion on the real system of its scheme (`…eq_real`). -/

section Games

variable {C : Type} [Fintype C]

-- `IND-CCA^PKE(b)` [1, Figure 1]: `(pk, sk) ← Gen`, `c* ← ⊥`; publish `pk`; the first
-- `(m₀, m₁)` gets `c* ← Enc(pk, m_b)`; on `c`, output `⊥` if `c = c*`, otherwise `Dec(sk, c)`.
system PKE.ChallengeCCA.Game(scheme : PublicKeyEncryption PK SK M C) (b : Bool) [DecidableEq PK] [DecidableEq M] [DecidableEq C] : PKEChallenge PK M C
  initialize
    keys ←$ scheme.gen
    cstar ← (none : Option C)
  on publicKey() → PK
    return keys.1
  on challenge(m₀ : M, m₁ : M) → Option C
    match cstar
    | some _ →
      return none
    | none →
      encryptions ←$ scheme.encryptions
      cstar ← some (encryptions (keys.1, if b then m₁ else m₀))
      return cstar
  on dec(c : C) → Option M
    if cstar = some c
      return none
    else
      return scheme.dec keys.2 c

-- `IND-CCA^KEM(b)` [1, Figure 1]: `(pk, sk) ← Gen`, `k₁ ← K`, `(c*, k₀) ← Enc(pk)`; the input
-- is `(pk, c*, k_b)`; on `c`, output `⊥` if `c = c*`, otherwise `Dec(sk, c)`.
system KEM.ChallengeCCA.Game(kem : KEM PK SK C₁ K) (b : Bool) [Nonempty K] [DecidableEq PK] [DecidableEq C₁] : KEMChallenge PK C₁ K
  initialize
    keys ←$ kem.gen
    k₁ ←$ 𝒰[K]
    encapsulations ←$ kem.encapsulations
  on input() → PK × C₁ × K
    return (keys.1, (encapsulations keys.1).1, if b then k₁ else (encapsulations keys.1).2)
  on dec(c : C₁) → Option K
    if c = (encapsulations keys.1).1
      return none
    else
      return kem.decaps keys.2 c

-- `IND-CCA^DEM(b)` [1, Figure 1]: `k ← K`, `c* ← ⊥`; the first `(m₀, m₁)` gets
-- `c* ← Enc(k, m_b)`; on `c`, output `⊥` if `c = c*`, otherwise `Dec(k, c)`.
system DEM.ChallengeCCA.Game(dem : SymmetricEncryption K M C₂) (b : Bool) [Nonempty K] [DecidableEq K] [DecidableEq M] [DecidableEq C₂] : ChallengeLeftRight M C₂
  initialize
    k ←$ 𝒰[K]
    cstar ← (none : Option C₂)
  on challenge(m₀ : M, m₁ : M) → Option C₂
    match cstar
    | some _ →
      return none
    | none →
      encryptions ←$ dem.encryptions
      cstar ← some (encryptions (k, if b then m₁ else m₀))
      return cstar
  on dec(c : C₂) → Option M
    if cstar = some c
      return none
    else
      return dem.dec k c

-- `Left` of `CPA` [2]: `(pk, sk) ← Gen`; publish `pk`; on `(m_L, m_R)`, output `Enc(pk, m_L)`.
system PKE.LORCPA.Left(scheme : PublicKeyEncryption PK SK M C) [DecidableEq PK] [DecidableEq M] : PKELeftRight PK M C
  initialize
    keys ←$ scheme.gen
  on publicKey() → PK
    return keys.1
  on enc(left : M, _right : M) → C
    encryptions ←$ scheme.encryptions
    return encryptions (keys.1, left)

-- `Right` of `CPA` [2]: `(pk, sk) ← Gen`; publish `pk`; on `(m_L, m_R)`, output `Enc(pk, m_R)`.
system PKE.LORCPA.Right(scheme : PublicKeyEncryption PK SK M C) [DecidableEq PK] [DecidableEq M] : PKELeftRight PK M C
  initialize
    keys ←$ scheme.gen
  on publicKey() → PK
    return keys.1
  on enc(_left : M, right : M) → C
    encryptions ←$ scheme.encryptions
    return encryptions (keys.1, right)

-- `Left` of `OTS` [2]: on `(m_L, m_R)`, output `Enc(k, m_L)` for a fresh uniform key `k`.
system Encryption.OTSLeft(dem : SymmetricEncryption K M C₂) [Nonempty K] [DecidableEq K] [DecidableEq M] : LeftRight M C₂
  on enc(left : M, _right : M) → C₂
    k ←$ 𝒰[K]
    encryptions ←$ dem.encryptions
    return encryptions (k, left)

-- `Right` of `OTS` [2]: on `(m_L, m_R)`, output `Enc(k, m_R)` for a fresh uniform key `k`.
system Encryption.OTSRight(dem : SymmetricEncryption K M C₂) [Nonempty K] [DecidableEq K] [DecidableEq M] : LeftRight M C₂
  on enc(_left : M, right : M) → C₂
    k ←$ 𝒰[K]
    encryptions ←$ dem.encryptions
    return encryptions (k, right)

end Games


/-- **KEM + DEM** [1, Figure 2]: `PKE.Gen = KEM.Gen`; `PKE.Enc(pk, m) = (c₁, DEM.Enc(k, m))` for
`(c₁, k) ← KEM.Enc(pk)`; `PKE.Dec(sk, (c₁, c₂))` is `⊥` if `KEM.Dec(sk, c₁) = ⊥` and
`DEM.Dec(k, c₂)` for `k = KEM.Dec(sk, c₁)` otherwise. -/
def scheme [DecidableEq C₁] [DecidableEq K] (kem : KEM PK SK C₁ K)
    (dem : SymmetricEncryption K M C₂) : PublicKeyEncryption PK SK M (C₁ × C₂) where
  gen := kem.gen
  enc pk m := Distribution.ProbDist.bind (kem.encaps pk) fun ck =>
    Distribution.ProbDist.map (fun c₂ => (ck.1, c₂)) (dem.enc ck.2 m)
  dec sk c := (kem.decaps sk c.1).bind fun k => dem.dec k c.2

-- `G₁(b)` [1, Figure 3]: `(pk, sk) ← KEM.Gen`, `(c₁*, k*) ← KEM.Enc(pk)` upfront, `c* ← ⊥`;
-- publish `pk`; the first `(m₀, m₁)` gets `c* := (c₁*, DEM.Enc(k*, m_b))`; on `c = (c₁, c₂)`, `⊥`
-- if `c = c*`, `DEM.Dec(k*, c₂)` if `c₁ = c₁*`, and otherwise `DEM.Dec(k, c₂)` for
-- `k = KEM.Dec(sk, c₁)`, or `⊥`.
system G₁(kem : KEM PK SK C₁ K) [DecidableEq PK] [DecidableEq C₁] [DecidableEq C₂] (dem : SymmetricEncryption K M C₂) [DecidableEq K] [DecidableEq M] (b : Bool) : PKEChallenge PK M (C₁ × C₂)
  initialize
    keys ←$ kem.gen
    encapsulations ←$ kem.encapsulations
    cstar ← (none : Option (C₁ × C₂))
  on publicKey() → PK
    return keys.1
  on challenge(m₀ : M, m₁ : M) → Option (C₁ × C₂)
    match cstar
    | some _ →
      return none
    | none →
      encryptions ←$ dem.encryptions
      cstar ← some ((encapsulations keys.1).1,
        encryptions ((encapsulations keys.1).2, if b then m₁ else m₀))
      return cstar
  on dec(c : C₁ × C₂) → Option M
    if cstar = some c
      return none
    else
      if c.1 = (encapsulations keys.1).1
        return dem.dec (encapsulations keys.1).2 c.2
      else
        return (kem.decaps keys.2 c.1).bind fun k => dem.dec k c.2

-- `G₂(b)` [1, Figure 3]: `G₁(b)` with `k* ← K` uniform in place of the encapsulated key.
system G₂(kem : KEM PK SK C₁ K) [DecidableEq PK] [DecidableEq C₁] [DecidableEq C₂] (dem : SymmetricEncryption K M C₂) [DecidableEq K] [DecidableEq M] [Nonempty K] (b : Bool) : PKEChallenge PK M (C₁ × C₂)
  initialize
    keys ←$ kem.gen
    encapsulations ←$ kem.encapsulations
    kstar ←$ 𝒰[K]
    cstar ← (none : Option (C₁ × C₂))
  on publicKey() → PK
    return keys.1
  on challenge(m₀ : M, m₁ : M) → Option (C₁ × C₂)
    match cstar
    | some _ →
      return none
    | none →
      encryptions ←$ dem.encryptions
      cstar ← some ((encapsulations keys.1).1, encryptions (kstar, if b then m₁ else m₀))
      return cstar
  on dec(c : C₁ × C₂) → Option M
    if cstar = some c
      return none
    else
      if c.1 = (encapsulations keys.1).1
        return dem.dec kstar c.2
      else
        return (kem.decaps keys.2 c.1).bind fun k => dem.dec k c.2

-- `B₁ b` [1, Figure 4]: on the KEM input `(pk, c₁*, k*)`, publish `pk`; the first `(m₀, m₁)`
-- gets `c* := (c₁*, DEM.Enc(k*, m_b))`; on `c = (c₁, c₂)`, `⊥` if `c = c*`, `DEM.Dec(k*, c₂)` if
-- `c₁ = c₁*`, and otherwise `DEM.Dec(k, c₂)` for `k ← kem.dec(c₁)`, or `⊥`.
converter B₁(PK C₁ : Type) [Fintype PK] [Fintype C₁] [DecidableEq C₁] [DecidableEq C₂] (dem : SymmetricEncryption K M C₂) [DecidableEq K] [DecidableEq M] (b : Bool) : PKEChallenge PK M (C₁ × C₂)
  inside kemGame : KEMChallenge PK C₁ K
  initialize
    cstar ← (none : Option (C₁ × C₂))
  on publicKey() → PK
    (pk, _c₁star, _kstar) ← kemGame.input()
    return pk
  on challenge(m₀ : M, m₁ : M) → Option (C₁ × C₂)
    (_pk, c₁star, kstar) ← kemGame.input()
    match cstar
    | some _ →
      return none
    | none →
      encryptions ←$ dem.encryptions
      cstar ← some (c₁star, encryptions (kstar, if b then m₁ else m₀))
      return cstar
  on dec(c : C₁ × C₂) → Option M
    (_pk, c₁star, kstar) ← kemGame.input()
    if cstar = some c
      return none
    else
      if c.1 = c₁star
        return dem.dec kstar c.2
      else
        k ← kemGame.dec(c.1)
        return k.bind fun k => dem.dec k c.2

-- `B₂` [1, Figure 4]: `(pk, sk) ← KEM.Gen`, `(c₁*, _) ← KEM.Enc(pk)`; publish `pk`; the first
-- `(m₀, m₁)` gets `c* := (c₁*, c₂*)` for the DEM challenge `c₂*`; on `c = (c₁, c₂)`, `⊥` if
-- `c = c*`, `demGame.dec(c₂)` if `c₁ = c₁*`, and otherwise `PKE.Dec(sk, c)`.
converter B₂(M C₂ : Type) [Fintype M] [Fintype C₂] [DecidableEq C₂] (kem : KEM PK SK C₁ K) [DecidableEq PK] [DecidableEq C₁] (dem : SymmetricEncryption K M C₂) : PKEChallenge PK M (C₁ × C₂)
  inside demGame : ChallengeLeftRight M C₂
  initialize
    keys ←$ kem.gen
    encapsulations ←$ kem.encapsulations
    cstar ← (none : Option (C₁ × C₂))
  on publicKey() → PK
    return keys.1
  on challenge(m₀ : M, m₁ : M) → Option (C₁ × C₂)
    c₂star ← demGame.challenge(m₀, m₁)
    match c₂star
    | none →
      return none
    | some c₂ →
      cstar ← some ((encapsulations keys.1).1, c₂)
      return cstar
  on dec(c : C₁ × C₂) → Option M
    if cstar = some c
      return none
    else
      if c.1 = (encapsulations keys.1).1
        m ← demGame.dec(c.2)
        return m
      else
        return (kem.decaps keys.2 c.1).bind fun k => dem.dec k c.2

-- `R1(E)` [2, 3]: publish `kem.publicKey()`; on `(m_L, m_R)`, `(c_kem, k_dem) ← kem.encaps()` and
-- return `(c_kem, DEM.Enc(k_dem, m_L))`.
converter R1(PK C₁ : Type) [Fintype PK] [Fintype C₁] (dem : SymmetricEncryption K M C₂) [DecidableEq K] [DecidableEq M] : PKELeftRight PK M (C₁ × C₂)
  inside kem : Encapsulation PK C₁ K
  on publicKey() → PK
    pk ← kem.publicKey()
    return pk
  on enc(mL : M, _mR : M) → C₁ × C₂
    (c_kem, k_dem) ← kem.encaps()
    encryptions ←$ dem.encryptions
    c_dem ← encryptions (k_dem, mL)
    return (c_kem, c_dem)

-- `R2(K)` [2, 3]: `(pk, sk) ← KEM.Gen`; publish `pk`; on `(m_L, m_R)`, return `(c_kem, c_dem)`
-- for `(c_kem, _) ← KEM.Enc(pk)` and `c_dem ← ots.enc(m_L, m_R)`.
converter 𝓡ₒ(M C₂ : Type) [Fintype M] [Fintype C₂] (kem : KEM PK SK C₁ K) [DecidableEq PK] : PKELeftRight PK M (C₁ × C₂)
  inside ots : LeftRight M C₂
  initialize
    keys ←$ kem.gen
  on publicKey() → PK
    return keys.1
  on enc(mL : M, mR : M) → C₁ × C₂
    encapsulations ←$ kem.encapsulations
    c_dem ← ots.enc(mL, mR)
    return ((encapsulations keys.1).1, c_dem)

-- `R3(E)` [2, 3]: publish `kem.publicKey()`; on `(m_L, m_R)`, `(c_kem, k_dem) ← kem.encaps()` and
-- return `(c_kem, DEM.Enc(k_dem, m_R))`.
converter R3(PK C₁ : Type) [Fintype PK] [Fintype C₁] (dem : SymmetricEncryption K M C₂) [DecidableEq K] [DecidableEq M] : PKELeftRight PK M (C₁ × C₂)
  inside kem : Encapsulation PK C₁ K
  on publicKey() → PK
    pk ← kem.publicKey()
    return pk
  on enc(_mL : M, mR : M) → C₁ × C₂
    (c_kem, k_dem) ← kem.encaps()
    encryptions ←$ dem.encryptions
    c_dem ← encryptions (k_dem, mR)
    return (c_kem, c_dem)

/-! ## The CPA reductions at per-label budgets

`R1(E)` and `R3(E)` call the public key from `publicKey`, and an encapsulation and their source
from `enc`: they are typed at per-label inside budgets, with no decapsulation
(`Interface.Converter.ofLabelBoundedProgram`). -/

section PerLabel

open CategoryTheory

/-- The KEM budget of `R1(E)` and `R3(E)`: the public key per public-key query, an encapsulation
per encryption, and no decapsulation. -/
abbrev kemBudget (q : PKELeftRight.Port → ℕ) : Encapsulation.Port → ℕ
  | .publicKey => q .publicKey
  | .encaps => q .enc
  | .decaps => 0

/-- The inside calls of `R1(E)` and `R3(E)` per procedure: the public key from `publicKey`, an
encapsulation and the source from `enc`. -/
def kemCalls : PKELeftRight.Port → Encapsulation.Port ⊕ Unit → ℕ
  | .publicKey, .inl .publicKey => 1
  | .enc, .inl .encaps => 1
  | .enc, .inr () => 1
  | _, _ => 0

variable [DecidableEq K] [DecidableEq M]

/-- `R1(E)` calls each inside label at most `kemCalls` times per procedure. -/
lemma R1.labelBounded (dem : SymmetricEncryption K M C₂) :
    (R1.body PK C₁ dem).LabelBounded kemCalls := by
  intro s o u
  cases o <;> simp only [R1.body] <;> cases s <;> dsimp only <;>
    repeat' (first
      | exact Program.labelCallBound_return _ _
      | (refine Program.labelCallBound_call _ _ _ (by decide) fun y => ?_))

/-- The inside interface of the program of `R1(E)`: the KEM beside the source. -/
abbrev R1.inside (PK C₁ : Type) [Fintype PK] [Fintype C₁] (dem : SymmetricEncryption K M C₂)
    (q : PKELeftRight.Port → ℕ) : Interface :=
  (Encapsulation.perPort PK C₁ K (Function.update (kemBudget q) .decaps 0)).tensor
    (Interface.source (lawType (R1.law1 PK C₁ dem)) (q .enc))

/-- The inside interface of `R1(E)` admits its per-label budget. -/
lemma R1.admits (dem : SymmetricEncryption K M C₂) (q : PKELeftRight.Port → ℕ) :
    (R1.inside PK C₁ dem q).AdmitsLabelBudget fun j => ∑ o, kemCalls o j * q o := by
  refine ((portBudget_admitsLabelBudget _ _ _ _).tensor (queryBudget_admitsLabelBudget _ _ _
    (fun _ => q .enc) (by simp))).mono fun j => ?_
  rcases j with (_ | _ | _) | _ <;> simp [Finset.univ, Fintype.elems, kemCalls]

/-- **`R1(E)` at per-port budgets**: the program of `R1(E)` at the per-label call bound
`kemCalls`, beside its source, into the KEM without decapsulation queries. -/
def R1.perLabel (PK C₁ : Type) [Fintype PK] [Fintype C₁] (dem : SymmetricEncryption K M C₂)
    (q : PKELeftRight.Port → ℕ) :
    PKELeftRight.perPort PK M (C₁ × C₂) q ⟶
      Encapsulation.perPort PK C₁ K (Function.update (kemBudget q) .decaps 0) :=
  Converter.ofLabelBoundedProgram (A := PKELeftRight.perPort PK M (C₁ × C₂) q)
      (B := R1.inside PK C₁ dem q) none (R1.body PK C₁ dem) (R1.bound_spec PK C₁ dem)
      kemCalls (R1.labelBounded dem) q (fun _ hd => hd.2) (R1.admits dem q) ≫
    Interface.rightContext _ (R1.randomness PK C₁ dem (q .enc))

/-- `R3(E)` calls each inside label at most `kemCalls` times per procedure. -/
lemma R3.labelBounded (dem : SymmetricEncryption K M C₂) :
    (R3.body PK C₁ dem).LabelBounded kemCalls := by
  intro s o u
  cases o <;> simp only [R3.body] <;> cases s <;> dsimp only <;>
    repeat' (first
      | exact Program.labelCallBound_return _ _
      | (refine Program.labelCallBound_call _ _ _ (by decide) fun y => ?_))

/-- The inside interface of the program of `R3(E)`: the KEM beside the source. -/
abbrev R3.inside (PK C₁ : Type) [Fintype PK] [Fintype C₁] (dem : SymmetricEncryption K M C₂)
    (q : PKELeftRight.Port → ℕ) : Interface :=
  (Encapsulation.perPort PK C₁ K (Function.update (kemBudget q) .decaps 0)).tensor
    (Interface.source (lawType (R3.law1 PK C₁ dem)) (q .enc))

/-- The inside interface of `R3(E)` admits its per-label budget. -/
lemma R3.admits (dem : SymmetricEncryption K M C₂) (q : PKELeftRight.Port → ℕ) :
    (R3.inside PK C₁ dem q).AdmitsLabelBudget fun j => ∑ o, kemCalls o j * q o := by
  refine ((portBudget_admitsLabelBudget _ _ _ _).tensor (queryBudget_admitsLabelBudget _ _ _
    (fun _ => q .enc) (by simp))).mono fun j => ?_
  rcases j with (_ | _ | _) | _ <;> simp [Finset.univ, Fintype.elems, kemCalls]

/-- **`R3(E)` at per-port budgets**: the program of `R3(E)` at the per-label call bound
`kemCalls`, beside its source, into the KEM without decapsulation queries. -/
def R3.perLabel (PK C₁ : Type) [Fintype PK] [Fintype C₁] (dem : SymmetricEncryption K M C₂)
    (q : PKELeftRight.Port → ℕ) :
    PKELeftRight.perPort PK M (C₁ × C₂) q ⟶
      Encapsulation.perPort PK C₁ K (Function.update (kemBudget q) .decaps 0) :=
  Converter.ofLabelBoundedProgram (A := PKELeftRight.perPort PK M (C₁ × C₂) q)
      (B := R3.inside PK C₁ dem q) none (R3.body PK C₁ dem) (R3.bound_spec PK C₁ dem)
      kemCalls (R3.labelBounded dem) q (fun _ hd => hd.2) (R3.admits dem q) ≫
    Interface.rightContext _ (R3.randomness PK C₁ dem (q .enc))

end PerLabel

variable [DecidableEq PK] [DecidableEq SK] [DecidableEq C₁] [DecidableEq K] [DecidableEq M]
  [DecidableEq C₂] [Nonempty K]

/-! ## The games as fresh sampling

Each game, and each adversary on its game, is presented as the probabilistic automaton that
samples afresh at each sampling statement; its step is the program of the component run against
fresh samples, and for an adversary against the step of the game inside. A component initializes
at its first query: from the state `none`, it samples its initial values and then answers as from
the initialized state. -/

/-! ### Presentations -/

/-- `G₁(b)` as fresh sampling. -/
noncomputable def G₁.freshSampling (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b : Bool) (q : ℕ) :
    FreshSampling (PKEChallenge PK M (C₁ × C₂) q) (G₁ kem dem b (budget := q)) :=
  ((FreshSampling.source (G₁.law1 kem dem b) _).parallel
    ((FreshSampling.source (G₁.law2 kem dem b) _).parallel
      (FreshSampling.source (G₁.law3 kem dem b) _))).ofProgram none _ _ _

/-- `G₂(b)` as fresh sampling. -/
noncomputable def G₂.freshSampling (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b : Bool) (q : ℕ) :
    FreshSampling (PKEChallenge PK M (C₁ × C₂) q) (G₂ kem dem b (budget := q)) :=
  ((FreshSampling.source (G₂.law1 kem dem b) _).parallel
    ((FreshSampling.source (G₂.law2 kem dem b) _).parallel
      ((FreshSampling.source (G₂.law3 kem dem b) _).parallel
        (FreshSampling.source (G₂.law4 kem dem b) _)))).ofProgram none _ _ _

/-- `IND-CCA^PKE(b)` as fresh sampling. -/
noncomputable def PKE.ChallengeCCA.Game.freshSampling {C : Type} [Fintype C] [DecidableEq C]
    (pke : PublicKeyEncryption PK SK M C) (b : Bool) (q : ℕ) :
    FreshSampling (PKEChallenge PK M C q) (PKE.ChallengeCCA.Game pke b (budget := q)) :=
  ((FreshSampling.source (PKE.ChallengeCCA.Game.law1 pke b) _).parallel
    (FreshSampling.source (PKE.ChallengeCCA.Game.law2 pke b) _)).ofProgram none _ _ _

/-- `IND-CCA^KEM(b)` as fresh sampling. -/
noncomputable def KEM.ChallengeCCA.Game.freshSampling (kem : KEM PK SK C₁ K) (b : Bool)
    (q : ℕ) :
    FreshSampling (KEMChallenge PK C₁ K q) (KEM.ChallengeCCA.Game kem b (budget := q)) :=
  ((FreshSampling.source (KEM.ChallengeCCA.Game.law1 kem b) _).parallel
    ((FreshSampling.source (KEM.ChallengeCCA.Game.law2 kem b) _).parallel
      (FreshSampling.source (KEM.ChallengeCCA.Game.law3 kem b) _))).ofProgram none _ _ _

/-- `IND-CCA^DEM(b)` as fresh sampling. -/
noncomputable def DEM.ChallengeCCA.Game.freshSampling (dem : SymmetricEncryption K M C₂)
    (b : Bool) (q : ℕ) :
    FreshSampling (ChallengeLeftRight M C₂ q) (DEM.ChallengeCCA.Game dem b (budget := q)) :=
  ((FreshSampling.source (DEM.ChallengeCCA.Game.law1 dem b) _).parallel
    (FreshSampling.source (DEM.ChallengeCCA.Game.law2 dem b) _)).ofProgram none _ _ _

/-- `B₁ b • IND-CCA^KEM(b')` as fresh sampling. -/
noncomputable def B₁.freshSamplingKEM (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b b' : Bool) (q : ℕ) :
    FreshSampling (PKEChallenge PK M (C₁ × C₂) q)
      (B₁ PK C₁ dem b (budget := q) • KEM.ChallengeCCA.Game kem b') :=
  FreshSampling.ofRightContext _
    (((KEM.ChallengeCCA.Game.freshSampling kem b' _).parallel
      (FreshSampling.source (B₁.law1 PK C₁ dem b) _)).ofProgram none _ _ _)

/-- `B₂ • IND-CCA^DEM(b)` as fresh sampling. -/
noncomputable def B₂.freshSamplingDEM (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b : Bool) (q : ℕ) :
    FreshSampling (PKEChallenge PK M (C₁ × C₂) q)
      (B₂ M C₂ kem dem (budget := q) • DEM.ChallengeCCA.Game dem b) :=
  FreshSampling.ofRightContext _
    (((DEM.ChallengeCCA.Game.freshSampling dem b _).parallel
      ((FreshSampling.source (B₂.law1 M C₂ kem dem) _).parallel
        (FreshSampling.source (B₂.law2 M C₂ kem dem) _))).ofProgram none _ _ _)

/-! ### Steps -/

/-- The fresh-sampling step of `G₁(b)`. -/
noncomputable abbrev G₁.freshStep (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b : Bool) :
    ProbStep (Option ((PK × SK) × (PK → C₁ × K) × Option (C₁ × C₂)) × Unit × Unit × Unit)
      PKEChallenge.Port (PKEChallenge.Input M (C₁ × C₂)) (PKEChallenge.Output PK M (C₁ × C₂)) :=
  (G₁.body kem dem b).probCombine
    (ProbStep.parallel (ProbStep.fresh (G₁.law1 kem dem b))
      (ProbStep.parallel (ProbStep.fresh (G₁.law2 kem dem b))
        (ProbStep.fresh (G₁.law3 kem dem b))))
    (G₁.bound_spec kem dem b)

/-- The fresh-sampling step of `G₂(b)`. -/
noncomputable abbrev G₂.freshStep (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b : Bool) :
    ProbStep (Option ((PK × SK) × (PK → C₁ × K) × K × Option (C₁ × C₂)) ×
        Unit × Unit × Unit × Unit)
      PKEChallenge.Port (PKEChallenge.Input M (C₁ × C₂)) (PKEChallenge.Output PK M (C₁ × C₂)) :=
  (G₂.body kem dem b).probCombine
    (ProbStep.parallel (ProbStep.fresh (G₂.law1 kem dem b))
      (ProbStep.parallel (ProbStep.fresh (G₂.law2 kem dem b))
        (ProbStep.parallel (ProbStep.fresh (G₂.law3 kem dem b))
          (ProbStep.fresh (G₂.law4 kem dem b)))))
    (G₂.bound_spec kem dem b)

/-- The fresh-sampling step of `IND-CCA^PKE(b)`. -/
noncomputable abbrev PKE.ChallengeCCA.Game.freshStep {C : Type} [Fintype C] [DecidableEq C]
    (pke : PublicKeyEncryption PK SK M C) (b : Bool) :
    ProbStep (Option ((PK × SK) × Option C) × Unit × Unit)
      PKEChallenge.Port (PKEChallenge.Input M C) (PKEChallenge.Output PK M C) :=
  (PKE.ChallengeCCA.Game.body pke b).probCombine
    (ProbStep.parallel (ProbStep.fresh (PKE.ChallengeCCA.Game.law1 pke b))
      (ProbStep.fresh (PKE.ChallengeCCA.Game.law2 pke b)))
    (PKE.ChallengeCCA.Game.bound_spec pke b)

/-- The fresh-sampling step of `IND-CCA^KEM(b)`. -/
noncomputable abbrev KEM.ChallengeCCA.Game.freshStep (kem : KEM PK SK C₁ K) (b : Bool) :
    ProbStep (Option ((PK × SK) × K × (PK → C₁ × K)) × Unit × Unit × Unit)
      KEMChallenge.Port (KEMChallenge.Input C₁) (KEMChallenge.Output PK C₁ K) :=
  (KEM.ChallengeCCA.Game.body kem b).probCombine
    (ProbStep.parallel (ProbStep.fresh (KEM.ChallengeCCA.Game.law1 kem b))
      (ProbStep.parallel (ProbStep.fresh (KEM.ChallengeCCA.Game.law2 kem b))
        (ProbStep.fresh (KEM.ChallengeCCA.Game.law3 kem b))))
    (KEM.ChallengeCCA.Game.bound_spec kem b)

/-- The fresh-sampling step of `IND-CCA^DEM(b)`. -/
noncomputable abbrev DEM.ChallengeCCA.Game.freshStep (dem : SymmetricEncryption K M C₂)
    (b : Bool) :
    ProbStep (Option (K × Option C₂) × Unit × Unit)
      ChallengeLeftRight.Port (ChallengeLeftRight.Input M C₂) (ChallengeLeftRight.Output M C₂) :=
  (DEM.ChallengeCCA.Game.body dem b).probCombine
    (ProbStep.parallel (ProbStep.fresh (DEM.ChallengeCCA.Game.law1 dem b))
      (ProbStep.fresh (DEM.ChallengeCCA.Game.law2 dem b)))
    (DEM.ChallengeCCA.Game.bound_spec dem b)

/-- The fresh-sampling step of `B₁ b` on a step of the KEM game. -/
noncomputable abbrev B₁.freshStep (dem : SymmetricEncryption K M C₂) (b : Bool) {R : Type}
    (stepR : ProbStep R KEMChallenge.Port (KEMChallenge.Input C₁)
      (KEMChallenge.Output PK C₁ K)) :
    ProbStep (Option (Option (C₁ × C₂)) × R × Unit)
      PKEChallenge.Port (PKEChallenge.Input M (C₁ × C₂)) (PKEChallenge.Output PK M (C₁ × C₂)) :=
  (B₁.body PK C₁ dem b).probCombine
    (ProbStep.parallel stepR (ProbStep.fresh (B₁.law1 PK C₁ dem b)))
    (B₁.bound_spec PK C₁ dem b)

/-- The fresh-sampling step of `B₂` on a step of the DEM game. -/
noncomputable abbrev B₂.freshStep (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    {R : Type} (stepR : ProbStep R ChallengeLeftRight.Port (ChallengeLeftRight.Input M C₂)
      (ChallengeLeftRight.Output M C₂)) :
    ProbStep (Option ((PK × SK) × (PK → C₁ × K) × Option (C₁ × C₂)) × R × Unit × Unit)
      PKEChallenge.Port (PKEChallenge.Input M (C₁ × C₂)) (PKEChallenge.Output PK M (C₁ × C₂)) :=
  (B₂.body M C₂ kem dem).probCombine
    (ProbStep.parallel stepR (ProbStep.parallel (ProbStep.fresh (B₂.law1 M C₂ kem dem))
      (ProbStep.fresh (B₂.law2 M C₂ kem dem))))
    (B₂.bound_spec M C₂ kem dem)

/-! ### `G₁(b)` -/

section G₁Steps

omit [DecidableEq SK] [Nonempty K]

/-- **`G₁(b)` on the public key.** -/
lemma G₁.outcome_publicKey (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (b : Bool)
    (keys : PK × SK) (e : PK → C₁ × K) (cs : Option (C₁ × C₂)) :
    (G₁.freshStep kem dem b).outcome (some (keys, e, cs), ((), ((), ()))) ⟨.publicKey, ()⟩ =
      Finsupp.single ((some (keys, e, cs), ((), ((), ()))),
        (⟨.publicKey, keys.1⟩ : Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (keys, e, cs), keys.1)) (by simp [G₁.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **`G₁(b)` on the first challenge**: `c* = (c₁*, DEM.Enc(k*, m_b))`. -/
lemma G₁.outcome_challenge (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (b : Bool)
    (keys : PK × SK) (e : PK → C₁ × K) (m₀ m₁ : M) :
    (G₁.freshStep kem dem b).outcome (some (keys, e, none), ((), ((), ())))
        ⟨.challenge, (m₀, m₁)⟩ =
      bindK dem.encryptions.1 fun E =>
        Finsupp.single ((some (keys, e, some ((e keys.1).1, E ((e keys.1).2,
            if b then m₁ else m₀))), ((), ((), ()))),
          (⟨.challenge, some ((e keys.1).1, E ((e keys.1).2, if b then m₁ else m₀))⟩ :
            Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val]
  rw [show G₁.bound kem dem b = 2 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inr (.inr ()), ()⟩) (by simp [G₁.body, callProg])]
  rw [ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun E _ => ?_
  rw [Program.probInvoke_inl
    (a := (some (keys, e, some ((e keys.1).1, E ((e keys.1).2, if b then m₁ else m₀))),
      some ((e keys.1).1, E ((e keys.1).2, if b then m₁ else m₀))))
    (by simp [G₁.body, callProg, returnProg, ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`G₁(b)` on a later challenge**: `⊥`. -/
lemma G₁.outcome_challenge_some (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b : Bool) (keys : PK × SK) (e : PK → C₁ × K) (cs : C₁ × C₂) (m₀ m₁ : M) :
    (G₁.freshStep kem dem b).outcome (some (keys, e, some cs), ((), ((), ())))
        ⟨.challenge, (m₀, m₁)⟩ =
      Finsupp.single ((some (keys, e, some cs), ((), ((), ()))),
          (⟨.challenge, none⟩ : Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (keys, e, some cs), none))
      (by simp [G₁.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **`G₁(b)` on a decryption**: `⊥` on `c*`, `DEM.Dec(k*, c₂)` under `c₁*`, otherwise
`DEM.Dec(k, c₂)` for `k = KEM.Dec(sk, c₁)`. -/
lemma G₁.outcome_dec (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (b : Bool)
    (keys : PK × SK) (e : PK → C₁ × K) (cs : Option (C₁ × C₂)) (c : C₁ × C₂) :
    (G₁.freshStep kem dem b).outcome (some (keys, e, cs), ((), ((), ()))) ⟨.dec, c⟩ =
      Finsupp.single ((some (keys, e, cs), ((), ((), ()))),
        (⟨.dec, if cs = some c then none else if c.1 = (e keys.1).1 then
          dem.dec (e keys.1).2 c.2 else (kem.decaps keys.2 c.1).bind fun k => dem.dec k c.2⟩ :
            Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (keys, e, cs), if cs = some c then none
      else if c.1 = (e keys.1).1 then dem.dec (e keys.1).2 c.2
      else (kem.decaps keys.2 c.1).bind fun k => dem.dec k c.2))
      (by by_cases h1 : cs = some c <;> by_cases h2 : c.1 = (e keys.1).1 <;>
        simp [G₁.body, returnProg, h1, h2])]
  simp [fTransform, ProbStep.tagged]

/-- **`G₁(b)` initializes at its first query**: the keys and the encapsulations are sampled. -/
lemma G₁.outcome_none (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (b : Bool)
    (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o) :
    (G₁.freshStep kem dem b).outcome (none, ((), ((), ()))) x =
      bindK kem.gen.1 fun keys => bindK kem.encapsulations.1 fun e =>
        (G₁.freshStep kem dem b).outcome (some (keys, e, none), ((), ((), ()))) x := by
  obtain ⟨o, u⟩ := x
  conv_lhs =>
    rw [ProbStep.outcome, Program.probCombine_val, show G₁.bound kem dem b = 2 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩) (by cases o <;> simp [G₁.body, callProg]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun keys _ => ?_
  conv_lhs =>
    rw [Program.probInvoke_succ_inr (q := ⟨.inr (.inl ()), ()⟩)
        (by cases o <;> simp [G₁.body, callProg, ProbStep.inlReply]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun e _ => ?_
  cases o
  · obtain ⟨⟩ := u
    rw [G₁.outcome_publicKey, Program.probInvoke_inl (a := (some (keys, e, none), keys.1))
      (by simp [G₁.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply])]
    simp [fTransform, ProbStep.tagged]
  · obtain ⟨m₀, m₁⟩ := u
    rw [G₁.outcome_challenge, Program.probInvoke_succ_inr (q := ⟨.inr (.inr ()), ()⟩)
        (by simp [G₁.body, callProg, ProbStep.inlReply, ProbStep.inrReply]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
    refine bindK_congr fun E _ => ?_
    rw [Program.probInvoke_inl
      (a := (some (keys, e, some ((e keys.1).1, E ((e keys.1).2, if b then m₁ else m₀))),
        some ((e keys.1).1, E ((e keys.1).2, if b then m₁ else m₀))))
      (by simp [G₁.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply])]
    simp [fTransform, ProbStep.tagged]
  · rw [G₁.outcome_dec, Program.probInvoke_inl (a := (some (keys, e, none),
      if u.1 = (e keys.1).1 then dem.dec (e keys.1).2 u.2
      else (kem.decaps keys.2 u.1).bind fun k => dem.dec k u.2))
      (by by_cases h2 : u.1 = (e keys.1).1 <;>
        simp [G₁.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply, h2])]
    simp [fTransform, ProbStep.tagged]

end G₁Steps

/-! ### `G₂(b)` -/

section G₂Steps

omit [DecidableEq SK]

/-- **`G₂(b)` on the public key.** -/
lemma G₂.outcome_publicKey (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (b : Bool)
    (keys : PK × SK) (e : PK → C₁ × K) (kstar : K) (cs : Option (C₁ × C₂)) :
    (G₂.freshStep kem dem b).outcome (some (keys, e, kstar, cs), ((), ((), ((), ()))))
        ⟨.publicKey, ()⟩ =
      Finsupp.single ((some (keys, e, kstar, cs), ((), ((), ((), ())))),
        (⟨.publicKey, keys.1⟩ : Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (keys, e, kstar, cs), keys.1))
      (by simp [G₂.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **`G₂(b)` on the first challenge**: `c* = (c₁*, DEM.Enc(k*, m_b))` for the uniform `k*`. -/
lemma G₂.outcome_challenge (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (b : Bool)
    (keys : PK × SK) (e : PK → C₁ × K) (kstar : K) (m₀ m₁ : M) :
    (G₂.freshStep kem dem b).outcome (some (keys, e, kstar, none), ((), ((), ((), ()))))
        ⟨.challenge, (m₀, m₁)⟩ =
      bindK dem.encryptions.1 fun E =>
        Finsupp.single ((some (keys, e, kstar, some ((e keys.1).1, E (kstar,
            if b then m₁ else m₀))), ((), ((), ((), ())))),
          (⟨.challenge, some ((e keys.1).1, E (kstar, if b then m₁ else m₀))⟩ :
            Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val]
  rw [show G₂.bound kem dem b = 3 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inr (.inr (.inr ())), ()⟩) (by simp [G₂.body, callProg])]
  rw [ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun E _ => ?_
  rw [Program.probInvoke_inl
    (a := (some (keys, e, kstar, some ((e keys.1).1, E (kstar, if b then m₁ else m₀))),
      some ((e keys.1).1, E (kstar, if b then m₁ else m₀))))
    (by simp [G₂.body, callProg, returnProg, ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`G₂(b)` on a later challenge**: `⊥`. -/
lemma G₂.outcome_challenge_some (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b : Bool) (keys : PK × SK) (e : PK → C₁ × K) (kstar : K) (cs : C₁ × C₂) (m₀ m₁ : M) :
    (G₂.freshStep kem dem b).outcome (some (keys, e, kstar, some cs), ((), ((), ((), ()))))
        ⟨.challenge, (m₀, m₁)⟩ =
      Finsupp.single ((some (keys, e, kstar, some cs), ((), ((), ((), ())))),
          (⟨.challenge, none⟩ : Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (keys, e, kstar, some cs), none))
      (by simp [G₂.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **`G₂(b)` on a decryption**: `⊥` on `c*`, `DEM.Dec(k*, c₂)` under `c₁*`, otherwise
`DEM.Dec(k, c₂)` for `k = KEM.Dec(sk, c₁)`. -/
lemma G₂.outcome_dec (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (b : Bool)
    (keys : PK × SK) (e : PK → C₁ × K) (kstar : K) (cs : Option (C₁ × C₂)) (c : C₁ × C₂) :
    (G₂.freshStep kem dem b).outcome (some (keys, e, kstar, cs), ((), ((), ((), ()))))
        ⟨.dec, c⟩ =
      Finsupp.single ((some (keys, e, kstar, cs), ((), ((), ((), ())))),
        (⟨.dec, if cs = some c then none else if c.1 = (e keys.1).1 then
          dem.dec kstar c.2 else (kem.decaps keys.2 c.1).bind fun k => dem.dec k c.2⟩ :
            Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (keys, e, kstar, cs), if cs = some c then none
      else if c.1 = (e keys.1).1 then dem.dec kstar c.2
      else (kem.decaps keys.2 c.1).bind fun k => dem.dec k c.2))
      (by by_cases h1 : cs = some c <;> by_cases h2 : c.1 = (e keys.1).1 <;>
        simp [G₂.body, returnProg, h1, h2])]
  simp [fTransform, ProbStep.tagged]

/-- **`G₂(b)` initializes at its first query**: the keys, the encapsulations and `k*` are
sampled. -/
lemma G₂.outcome_none (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (b : Bool)
    (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o) :
    (G₂.freshStep kem dem b).outcome (none, ((), ((), ((), ())))) x =
      bindK kem.gen.1 fun keys => bindK kem.encapsulations.1 fun e => bindK (𝒰[K]).1 fun kstar =>
        (G₂.freshStep kem dem b).outcome (some (keys, e, kstar, none), ((), ((), ((), ())))) x := by
  obtain ⟨o, u⟩ := x
  conv_lhs =>
    rw [ProbStep.outcome, Program.probCombine_val, show G₂.bound kem dem b = 3 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩) (by cases o <;> simp [G₂.body, callProg]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun keys _ => ?_
  conv_lhs =>
    rw [Program.probInvoke_succ_inr (q := ⟨.inr (.inl ()), ()⟩)
        (by cases o <;> simp [G₂.body, callProg, ProbStep.inlReply]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun e _ => ?_
  conv_lhs =>
    rw [Program.probInvoke_succ_inr (q := ⟨.inr (.inr (.inl ())), ()⟩)
        (by cases o <;> simp [G₂.body, callProg, ProbStep.inlReply, ProbStep.inrReply]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun kstar _ => ?_
  cases o
  · obtain ⟨⟩ := u
    rw [G₂.outcome_publicKey, Program.probInvoke_inl (a := (some (keys, e, kstar, none), keys.1))
      (by simp [G₂.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply])]
    simp [fTransform, ProbStep.tagged]
  · obtain ⟨m₀, m₁⟩ := u
    rw [G₂.outcome_challenge, Program.probInvoke_succ_inr (q := ⟨.inr (.inr (.inr ())), ()⟩)
        (by simp [G₂.body, callProg, ProbStep.inlReply, ProbStep.inrReply]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
    refine bindK_congr fun E _ => ?_
    rw [Program.probInvoke_inl
      (a := (some (keys, e, kstar, some ((e keys.1).1, E (kstar, if b then m₁ else m₀))),
        some ((e keys.1).1, E (kstar, if b then m₁ else m₀))))
      (by simp [G₂.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply])]
    simp [fTransform, ProbStep.tagged]
  · rw [G₂.outcome_dec, Program.probInvoke_inl (a := (some (keys, e, kstar, none),
      if u.1 = (e keys.1).1 then dem.dec kstar u.2
      else (kem.decaps keys.2 u.1).bind fun k => dem.dec k u.2))
      (by by_cases h2 : u.1 = (e keys.1).1 <;>
        simp [G₂.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply, h2])]
    simp [fTransform, ProbStep.tagged]

end G₂Steps

/-! ### `IND-CCA^PKE(b)` -/

section PKE

omit [DecidableEq SK]

variable {C : Type} [Fintype C] [DecidableEq C]

/-- **`IND-CCA^PKE(b)` on the public key.** -/
lemma PKE.ChallengeCCA.Game.outcome_publicKey (pke : PublicKeyEncryption PK SK M C) (b : Bool)
    (keys : PK × SK) (cs : Option C) :
    (PKE.ChallengeCCA.Game.freshStep pke b).outcome (some (keys, cs), ((), ()))
        ⟨.publicKey, ()⟩ =
      Finsupp.single ((some (keys, cs), ((), ())),
        (⟨.publicKey, keys.1⟩ : Σ o, PKEChallenge.Output PK M C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (keys, cs), keys.1))
      (by simp [PKE.ChallengeCCA.Game.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **`IND-CCA^PKE(b)` on the first challenge**: `c* ← Enc(pk, m_b)`. -/
lemma PKE.ChallengeCCA.Game.outcome_challenge (pke : PublicKeyEncryption PK SK M C) (b : Bool)
    (keys : PK × SK) (m₀ m₁ : M) :
    (PKE.ChallengeCCA.Game.freshStep pke b).outcome (some (keys, none), ((), ()))
        ⟨.challenge, (m₀, m₁)⟩ =
      bindK pke.encryptions.1 fun E =>
        Finsupp.single ((some (keys, some (E (keys.1, if b then m₁ else m₀))), ((), ())),
          (⟨.challenge, some (E (keys.1, if b then m₁ else m₀))⟩ :
            Σ o, PKEChallenge.Output PK M C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val]
  rw [show PKE.ChallengeCCA.Game.bound pke b = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
      (by simp [PKE.ChallengeCCA.Game.body, callProg]),
    ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun E _ => ?_
  rw [Program.probInvoke_inl
    (a := (some (keys, some (E (keys.1, if b then m₁ else m₀))),
      some (E (keys.1, if b then m₁ else m₀))))
    (by simp [PKE.ChallengeCCA.Game.body, callProg, returnProg, ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`IND-CCA^PKE(b)` on a later challenge**: `⊥`. -/
lemma PKE.ChallengeCCA.Game.outcome_challenge_some (pke : PublicKeyEncryption PK SK M C)
    (b : Bool) (keys : PK × SK) (c : C) (m₀ m₁ : M) :
    (PKE.ChallengeCCA.Game.freshStep pke b).outcome (some (keys, some c), ((), ()))
        ⟨.challenge, (m₀, m₁)⟩ =
      Finsupp.single ((some (keys, some c), ((), ())),
        (⟨.challenge, none⟩ : Σ o, PKEChallenge.Output PK M C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (keys, some c), none))
      (by simp [PKE.ChallengeCCA.Game.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **`IND-CCA^PKE(b)` on a decryption**: `⊥` on `c*`, otherwise `Dec(sk, c)`. -/
lemma PKE.ChallengeCCA.Game.outcome_dec (pke : PublicKeyEncryption PK SK M C) (b : Bool)
    (keys : PK × SK) (cs : Option C) (c : C) :
    (PKE.ChallengeCCA.Game.freshStep pke b).outcome (some (keys, cs), ((), ())) ⟨.dec, c⟩ =
      Finsupp.single ((some (keys, cs), ((), ())),
        (⟨.dec, if cs = some c then none else pke.dec keys.2 c⟩ :
          Σ o, PKEChallenge.Output PK M C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (keys, cs), if cs = some c then none
      else pke.dec keys.2 c))
      (by by_cases h : cs = some c <;> simp [PKE.ChallengeCCA.Game.body, returnProg, h])]
  simp [fTransform, ProbStep.tagged]

/-- **`IND-CCA^PKE(b)` initializes at its first query**: the keys are sampled. -/
lemma PKE.ChallengeCCA.Game.outcome_none (pke : PublicKeyEncryption PK SK M C) (b : Bool)
    (x : Σ o, PKEChallenge.Input M C o) :
    (PKE.ChallengeCCA.Game.freshStep pke b).outcome (none, ((), ())) x =
      bindK pke.gen.1 fun keys => (PKE.ChallengeCCA.Game.freshStep pke b).outcome
        (some (keys, none), ((), ())) x := by
  obtain ⟨o, u⟩ := x
  conv_lhs =>
    rw [ProbStep.outcome, Program.probCombine_val,
      show PKE.ChallengeCCA.Game.bound pke b = 1 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩)
        (by cases o <;> simp [PKE.ChallengeCCA.Game.body, callProg]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun keys _ => ?_
  cases o
  · obtain ⟨⟩ := u
    rw [PKE.ChallengeCCA.Game.outcome_publicKey,
      Program.probInvoke_inl (a := (some (keys, none), keys.1))
        (by simp [PKE.ChallengeCCA.Game.body, callProg, returnProg, ProbStep.inlReply])]
    simp [fTransform, ProbStep.tagged]
  · obtain ⟨m₀, m₁⟩ := u
    rw [PKE.ChallengeCCA.Game.outcome_challenge, Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
        (by simp [PKE.ChallengeCCA.Game.body, callProg, ProbStep.inlReply]),
      ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
    refine bindK_congr fun E _ => ?_
    rw [Program.probInvoke_inl
      (a := (some (keys, some (E (keys.1, if b then m₁ else m₀))),
        some (E (keys.1, if b then m₁ else m₀))))
      (by simp [PKE.ChallengeCCA.Game.body, callProg, returnProg, ProbStep.inlReply,
        ProbStep.inrReply])]
    simp [fTransform, ProbStep.tagged]
  · rw [PKE.ChallengeCCA.Game.outcome_dec, Program.probInvoke_inl (a := (some (keys, none),
      pke.dec keys.2 u))
      (by simp [PKE.ChallengeCCA.Game.body, callProg, returnProg, ProbStep.inlReply])]
    simp [fTransform, ProbStep.tagged]

end PKE

/-! ### `IND-CCA^KEM(b)` -/

section KEMSteps

omit [DecidableEq SK] [DecidableEq K]

/-- **`IND-CCA^KEM(b)` initializes at its first input**: the keys, `k₁` and the encapsulations
are sampled. -/
lemma KEM.ChallengeCCA.Game.outcome_input_none (kem : KEM PK SK C₁ K) (b : Bool) :
    (KEM.ChallengeCCA.Game.freshStep kem b).outcome (none, ((), ((), ()))) ⟨.input, ()⟩ =
      bindK kem.gen.1 fun keys => bindK (𝒰[K]).1 fun k₁ => bindK kem.encapsulations.1 fun e =>
        Finsupp.single ((some (keys, k₁, e), ((), ((), ()))),
          (⟨.input, (keys.1, (e keys.1).1, if b then k₁ else (e keys.1).2)⟩ :
            Σ i, KEMChallenge.Output PK C₁ K i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val]
  rw [show KEM.ChallengeCCA.Game.bound kem b = 2 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩)
      (by simp [KEM.ChallengeCCA.Game.body, callProg])]
  rw [ProbStep.outcome_parallel_inl]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun keys _ => ?_
  rw [Program.probInvoke_succ_inr (q := ⟨.inr (.inl ()), ()⟩)
      (by simp [KEM.ChallengeCCA.Game.body, callProg, ProbStep.inlReply]),
    ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inl]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun k₁ _ => ?_
  rw [Program.probInvoke_succ_inr (q := ⟨.inr (.inr ()), ()⟩)
      (by simp [KEM.ChallengeCCA.Game.body, callProg, ProbStep.inlReply, ProbStep.inrReply]),
    ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun e _ => ?_
  rw [Program.probInvoke_inl
    (a := (some (keys, k₁, e), (keys.1, (e keys.1).1, if b then k₁ else (e keys.1).2)))
    (by simp [KEM.ChallengeCCA.Game.body, callProg, returnProg, ProbStep.inlReply,
      ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`IND-CCA^KEM(b)` on the input**: `(pk, c*, k_b)`. -/
lemma KEM.ChallengeCCA.Game.outcome_input (kem : KEM PK SK C₁ K) (b : Bool)
    (keys : PK × SK) (k₁ : K) (e : PK → C₁ × K) :
    (KEM.ChallengeCCA.Game.freshStep kem b).outcome (some (keys, k₁, e), ((), ((), ())))
        ⟨.input, ()⟩ =
      Finsupp.single ((some (keys, k₁, e), ((), ((), ()))),
        (⟨.input, (keys.1, (e keys.1).1, if b then k₁ else (e keys.1).2)⟩ :
          Σ i, KEMChallenge.Output PK C₁ K i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl
      (a := (some (keys, k₁, e), (keys.1, (e keys.1).1, if b then k₁ else (e keys.1).2)))
      (by simp [KEM.ChallengeCCA.Game.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **`IND-CCA^KEM(b)` on a decapsulation**: `⊥` on `c*`, otherwise `Dec(sk, c)`. -/
lemma KEM.ChallengeCCA.Game.outcome_dec (kem : KEM PK SK C₁ K) (b : Bool)
    (keys : PK × SK) (k₁ : K) (e : PK → C₁ × K) (c₁ : C₁) :
    (KEM.ChallengeCCA.Game.freshStep kem b).outcome (some (keys, k₁, e), ((), ((), ())))
        ⟨.dec, c₁⟩ =
      Finsupp.single ((some (keys, k₁, e), ((), ((), ()))),
        (⟨.dec, if c₁ = (e keys.1).1 then none else kem.decaps keys.2 c₁⟩ :
          Σ i, KEMChallenge.Output PK C₁ K i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl
      (a := (some (keys, k₁, e), if c₁ = (e keys.1).1 then none else kem.decaps keys.2 c₁))
      (by by_cases h : c₁ = (e keys.1).1 <;> simp [KEM.ChallengeCCA.Game.body, returnProg, h])]
  simp [fTransform, ProbStep.tagged]

/-- **`IND-CCA^KEM(b)` initializes at its first input**, as a mixture of initialized states. -/
lemma KEM.ChallengeCCA.Game.outcome_input_init (kem : KEM PK SK C₁ K) (b : Bool) :
    (KEM.ChallengeCCA.Game.freshStep kem b).outcome (none, ((), ((), ()))) ⟨.input, ()⟩ =
      bindK (bindK kem.gen.1 fun keys => bindK (𝒰[K]).1 fun k₁ =>
          bindK kem.encapsulations.1 fun e => Finsupp.single (some (keys, k₁, e), ((), ((), ()))) 1)
        fun r => (KEM.ChallengeCCA.Game.freshStep kem b).outcome r ⟨.input, ()⟩ := by
  rw [KEM.ChallengeCCA.Game.outcome_input_none]
  simp only [bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun keys _ => bindK_congr fun k₁ _ => bindK_congr fun e _ => ?_
  exact (KEM.ChallengeCCA.Game.outcome_input kem b keys k₁ e).symm

end KEMSteps

/-! ### `IND-CCA^DEM(b)` -/

/-- **`IND-CCA^DEM(b)` on the first challenge, uninitialized**: `k ← K`, `c* ← Enc(k, m_b)`. -/
lemma DEM.ChallengeCCA.Game.outcome_challenge_none (dem : SymmetricEncryption K M C₂)
    (b : Bool) (m₀ m₁ : M) :
    (DEM.ChallengeCCA.Game.freshStep dem b).outcome (none, ((), ())) ⟨.challenge, (m₀, m₁)⟩ =
      bindK (𝒰[K]).1 fun k => bindK dem.encryptions.1 fun E =>
        Finsupp.single ((some (k, some (E (k, if b then m₁ else m₀))), ((), ())),
          (⟨.challenge, some (E (k, if b then m₁ else m₀))⟩ :
            Σ i, ChallengeLeftRight.Output M C₂ i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val]
  rw [show DEM.ChallengeCCA.Game.bound dem b = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩)
      (by simp [DEM.ChallengeCCA.Game.body, callProg]),
    ProbStep.outcome_parallel_inl]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun k _ => ?_
  rw [Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
      (by simp [DEM.ChallengeCCA.Game.body, callProg, ProbStep.inlReply]),
    ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun E _ => ?_
  rw [Program.probInvoke_inl
    (a := (some (k, some (E (k, if b then m₁ else m₀))), some (E (k, if b then m₁ else m₀))))
    (by simp [DEM.ChallengeCCA.Game.body, callProg, returnProg, ProbStep.inlReply,
      ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`IND-CCA^DEM(b)` on the first challenge**: `c* ← Enc(k, m_b)`. -/
lemma DEM.ChallengeCCA.Game.outcome_challenge (dem : SymmetricEncryption K M C₂) (b : Bool)
    (k : K) (m₀ m₁ : M) :
    (DEM.ChallengeCCA.Game.freshStep dem b).outcome (some (k, none), ((), ()))
        ⟨.challenge, (m₀, m₁)⟩ =
      bindK dem.encryptions.1 fun E =>
        Finsupp.single ((some (k, some (E (k, if b then m₁ else m₀))), ((), ())),
          (⟨.challenge, some (E (k, if b then m₁ else m₀))⟩ :
            Σ i, ChallengeLeftRight.Output M C₂ i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val]
  rw [show DEM.ChallengeCCA.Game.bound dem b = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
      (by simp [DEM.ChallengeCCA.Game.body, callProg]),
    ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun E _ => ?_
  rw [Program.probInvoke_inl
    (a := (some (k, some (E (k, if b then m₁ else m₀))), some (E (k, if b then m₁ else m₀))))
    (by simp [DEM.ChallengeCCA.Game.body, callProg, returnProg, ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`IND-CCA^DEM(b)` on a later challenge**: `⊥`. -/
lemma DEM.ChallengeCCA.Game.outcome_challenge_some (dem : SymmetricEncryption K M C₂)
    (b : Bool) (k : K) (c₂ : C₂) (m₀ m₁ : M) :
    (DEM.ChallengeCCA.Game.freshStep dem b).outcome (some (k, some c₂), ((), ()))
        ⟨.challenge, (m₀, m₁)⟩ =
      Finsupp.single ((some (k, some c₂), ((), ())),
        (⟨.challenge, none⟩ : Σ i, ChallengeLeftRight.Output M C₂ i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (k, some c₂), none))
      (by simp [DEM.ChallengeCCA.Game.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **`IND-CCA^DEM(b)` on a decryption, uninitialized**: `k ← K`, then `Dec(k, c)`. -/
lemma DEM.ChallengeCCA.Game.outcome_dec_none (dem : SymmetricEncryption K M C₂) (b : Bool)
    (c₂ : C₂) :
    (DEM.ChallengeCCA.Game.freshStep dem b).outcome (none, ((), ())) ⟨.dec, c₂⟩ =
      bindK (𝒰[K]).1 fun k => Finsupp.single ((some (k, none), ((), ())),
        (⟨.dec, dem.dec k c₂⟩ : Σ i, ChallengeLeftRight.Output M C₂ i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val]
  rw [show DEM.ChallengeCCA.Game.bound dem b = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩)
      (by simp [DEM.ChallengeCCA.Game.body, callProg]),
    ProbStep.outcome_parallel_inl]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun k _ => ?_
  rw [Program.probInvoke_inl (a := (some (k, none), dem.dec k c₂))
    (by simp [DEM.ChallengeCCA.Game.body, callProg, returnProg, ProbStep.inlReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`IND-CCA^DEM(b)` on a decryption**: `⊥` on `c*`, otherwise `Dec(k, c)`. -/
lemma DEM.ChallengeCCA.Game.outcome_dec (dem : SymmetricEncryption K M C₂) (b : Bool)
    (k : K) (cd : Option C₂) (c₂ : C₂) :
    (DEM.ChallengeCCA.Game.freshStep dem b).outcome (some (k, cd), ((), ())) ⟨.dec, c₂⟩ =
      Finsupp.single ((some (k, cd), ((), ())),
        (⟨.dec, if cd = some c₂ then none else dem.dec k c₂⟩ :
          Σ i, ChallengeLeftRight.Output M C₂ i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (k, cd), if cd = some c₂ then none else dem.dec k c₂))
      (by by_cases h : cd = some c₂ <;> simp [DEM.ChallengeCCA.Game.body, returnProg, h])]
  simp [fTransform, ProbStep.tagged]

/-! ### `B₁ b` -/

section B₁

omit [DecidableEq PK] [Nonempty K]

variable {R : Type} (stepR : ProbStep R KEMChallenge.Port (KEMChallenge.Input C₁)
  (KEMChallenge.Output PK C₁ K))

/-- **`B₁ b` reads the KEM input first**: on a KEM game whose input initializes it from a law of
states, `B₁ b` on it is the mixture over that law. -/
lemma B₁.outcome_bindK (dem : SymmetricEncryption K M C₂) (b : Bool)
    (cB : Option (Option (C₁ × C₂))) (r : R) (ρ : Distribution R)
    (h : stepR.outcome r ⟨.input, ()⟩ = bindK ρ fun r' => stepR.outcome r' ⟨.input, ()⟩)
    (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o) :
    (B₁.freshStep dem b stepR).outcome (cB, (r, ())) x =
      bindK ρ fun r' => (B₁.freshStep dem b stepR).outcome (cB, (r', ())) x := by
  obtain ⟨o, u⟩ := x
  have h0 : B₁.body PK C₁ dem b cB o u [] = .inr ⟨.inl .input, ()⟩ := by
    cases o <;> cases cB <;> simp [B₁.body, callProg]
  have hb : B₁.bound PK C₁ dem b = 1 + 1 := rfl
  conv_lhs => rw [ProbStep.outcome, Program.probCombine_val, hb,
    Program.probInvoke_succ_inr h0, ProbStep.outcome_parallel_inl, h]
  conv_rhs => enter [2, r']; rw [ProbStep.outcome, Program.probCombine_val, hb,
    Program.probInvoke_succ_inr h0, ProbStep.outcome_parallel_inl]
  simp only [fTransform_bindK, bindK_bindK, bindK_fTransform, Function.comp_def]

/-- **`B₁ b` on the public key**: `pk` of the KEM input. -/
lemma B₁.outcome_publicKey (dem : SymmetricEncryption K M C₂) (b : Bool)
    (cB : Option (Option (C₁ × C₂))) (r : R) (v : PK × C₁ × K)
    (hin : stepR.outcome r ⟨.input, ()⟩ = Finsupp.single (r, ⟨.input, v⟩) 1) :
    (B₁.freshStep dem b stepR).outcome (cB, (r, ())) ⟨.publicKey, ()⟩ =
      Finsupp.single ((some (cB.getD none), (r, ())),
        (⟨.publicKey, v.1⟩ : Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val]
  rw [show B₁.bound PK C₁ dem b = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl .input, ()⟩)
      (by cases cB <;> simp [B₁.body, callProg])]
  rw [ProbStep.outcome_parallel_inl, hin]
  simp only [fTransform_single, bindK_single, one_smul]
  rw [Program.probInvoke_inl (a := (some (cB.getD none), v.1))
    (by cases cB <;> simp [B₁.body, callProg, returnProg, ProbStep.inlReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`B₁ b` on the first challenge**: `c* = (c₁*, DEM.Enc(k*, m_b))` for the KEM input
`(pk, c₁*, k*)`. -/
lemma B₁.outcome_challenge (dem : SymmetricEncryption K M C₂) (b : Bool)
    (cB : Option (Option (C₁ × C₂))) (hcB : cB.getD none = none) (r : R) (v : PK × C₁ × K)
    (hin : stepR.outcome r ⟨.input, ()⟩ = Finsupp.single (r, ⟨.input, v⟩) 1) (m₀ m₁ : M) :
    (B₁.freshStep dem b stepR).outcome (cB, (r, ())) ⟨.challenge, (m₀, m₁)⟩ =
      bindK (B₁.law1 PK C₁ dem b).1 fun E =>
        Finsupp.single ((some (some (v.2.1, E (v.2.2, if b then m₁ else m₀))), (r, ())),
          (⟨.challenge, some (v.2.1, E (v.2.2, if b then m₁ else m₀))⟩ :
            Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  have hcB' : cB = none ∨ cB = some none := by
    rcases cB with _ | _ | _ <;> simp_all
  rw [ProbStep.outcome, Program.probCombine_val]
  rw [show B₁.bound PK C₁ dem b = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl .input, ()⟩)
      (by rcases hcB' with rfl | rfl <;> simp [B₁.body, callProg])]
  rw [ProbStep.outcome_parallel_inl, hin]
  simp only [fTransform_single, bindK_single, one_smul]
  rw [Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
      (by rcases hcB' with rfl | rfl <;> simp [B₁.body, callProg, ProbStep.inlReply])]
  rw [ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun E _ => ?_
  rw [Program.probInvoke_inl
    (a := (some (some (v.2.1, E (v.2.2, if b then m₁ else m₀))),
      some (v.2.1, E (v.2.2, if b then m₁ else m₀))))
    (by rcases hcB' with rfl | rfl <;> simp [B₁.body, callProg, returnProg, ProbStep.inlReply,
      ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`B₁ b` on a later challenge**: `⊥`. -/
lemma B₁.outcome_challenge_some (dem : SymmetricEncryption K M C₂) (b : Bool)
    (cs : C₁ × C₂) (r : R) (v : PK × C₁ × K)
    (hin : stepR.outcome r ⟨.input, ()⟩ = Finsupp.single (r, ⟨.input, v⟩) 1) (m₀ m₁ : M) :
    (B₁.freshStep dem b stepR).outcome (some (some cs), (r, ())) ⟨.challenge, (m₀, m₁)⟩ =
      Finsupp.single ((some (some cs), (r, ())),
          (⟨.challenge, none⟩ : Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val]
  rw [show B₁.bound PK C₁ dem b = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl .input, ()⟩) (by simp [B₁.body, callProg])]
  rw [ProbStep.outcome_parallel_inl, hin]
  simp only [fTransform_single, bindK_single, one_smul]
  rw [Program.probInvoke_inl (a := (some (some cs), none))
    (by simp [B₁.body, callProg, returnProg, ProbStep.inlReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`B₁ b` on a decryption**: `⊥` on `c*`, `DEM.Dec(k*, c₂)` under `c₁*`, otherwise
`DEM.Dec(k, c₂)` for the decapsulation `k` of the KEM game. -/
lemma B₁.outcome_dec (dem : SymmetricEncryption K M C₂) (b : Bool)
    (cB : Option (Option (C₁ × C₂))) (r : R) (v : PK × C₁ × K)
    (hin : stepR.outcome r ⟨.input, ()⟩ = Finsupp.single (r, ⟨.input, v⟩) 1)
    (kd : C₁ → Option K)
    (hdec : ∀ c₁, c₁ ≠ v.2.1 → stepR.outcome r ⟨.dec, c₁⟩ = Finsupp.single (r, ⟨.dec, kd c₁⟩) 1)
    (c : C₁ × C₂) :
    (B₁.freshStep dem b stepR).outcome (cB, (r, ())) ⟨.dec, c⟩ =
      Finsupp.single ((some (cB.getD none), (r, ())),
        (⟨.dec, if cB.getD none = some c then none else if c.1 = v.2.1 then dem.dec v.2.2 c.2
          else (kd c.1).bind fun k => dem.dec k c.2⟩ :
            Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  obtain ⟨pk, c₁star, kstar⟩ := v
  rw [ProbStep.outcome, Program.probCombine_val]
  rw [show B₁.bound PK C₁ dem b = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl .input, ()⟩)
      (by cases cB <;> simp [B₁.body, callProg])]
  rw [ProbStep.outcome_parallel_inl, hin]
  simp only [fTransform_single, bindK_single, one_smul]
  by_cases h1 : cB.getD none = some c
  · rw [Program.probInvoke_inl (a := (some (cB.getD none), none))
      (by rcases cB with _ | _ | _ <;> simp_all [B₁.body, callProg, returnProg, ProbStep.inlReply])]
    simp [fTransform, ProbStep.tagged, h1]
  by_cases h2 : c.1 = c₁star
  · rw [Program.probInvoke_inl (a := (some (cB.getD none), dem.dec kstar c.2))
      (by rcases cB with _ | _ | _ <;> simp_all [B₁.body, callProg, returnProg, ProbStep.inlReply])]
    simp [fTransform, ProbStep.tagged, h1, h2]
  rw [Program.probInvoke_succ_inr (q := ⟨.inl .dec, c.1⟩)
      (by rcases cB with _ | _ | _ <;> simp_all [B₁.body, callProg, ProbStep.inlReply])]
  rw [ProbStep.outcome_parallel_inl, hdec c.1 h2]
  simp only [fTransform_single, bindK_single, one_smul]
  rw [Program.probInvoke_inl (a := (some (cB.getD none), (kd c.1).bind fun k => dem.dec k c.2))
    (by rcases cB with _ | _ | _ <;> simp_all [B₁.body, callProg, returnProg, ProbStep.inlReply])]
  simp [fTransform, ProbStep.tagged, h1, h2]

end B₁

section B₁KEM

omit [DecidableEq SK]

/-- **`B₁ b` initializes `IND-CCA^KEM(b')` at its first query.** -/
lemma B₁.outcome_initKEM (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (b b' : Bool)
    (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o) :
    (B₁.freshStep dem b (KEM.ChallengeCCA.Game.freshStep kem b')).outcome
        (none, ((none, ((), ((), ()))), ())) x =
      bindK kem.gen.1 fun keys => bindK (𝒰[K]).1 fun k₁ => bindK kem.encapsulations.1 fun e =>
        (B₁.freshStep dem b (KEM.ChallengeCCA.Game.freshStep kem b')).outcome
          (none, ((some (keys, k₁, e), ((), ((), ()))), ())) x := by
  rw [B₁.outcome_bindK _ dem b none _ _ (KEM.ChallengeCCA.Game.outcome_input_init kem b')]
  simp only [bindK_bindK, bindK_single, one_smul]

/-- **`B₁ b` on an initialized `IND-CCA^KEM(b')`** keeps the state of the KEM game. -/
lemma B₁.mem_support_outcome_KEM (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b b' : Bool) (cB : Option (Option (C₁ × C₂))) (keys : PK × SK) (k₁ : K)
    (e : PK → C₁ × K) (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o) (p)
    (hp : p ∈ ((B₁.freshStep dem b (KEM.ChallengeCCA.Game.freshStep kem b')).outcome
        (cB, ((some (keys, k₁, e), ((), ((), ()))), ())) x).support) :
    p.1.2.1.1 = some (keys, k₁, e) := by
  obtain ⟨o, u⟩ := x
  have hin := KEM.ChallengeCCA.Game.outcome_input kem b' keys k₁ e
  cases o
  · obtain ⟨⟩ := u
    rw [B₁.outcome_publicKey _ dem b cB _ _ hin] at hp
    rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
  · obtain ⟨m₀, m₁⟩ := u
    rcases cB with _ | _ | cs
    · rw [B₁.outcome_challenge _ dem b none rfl _ _ hin] at hp
      obtain ⟨E, -, hp⟩ := mem_support_bindK hp
      rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
    · rw [B₁.outcome_challenge _ dem b (some none) rfl _ _ hin] at hp
      obtain ⟨E, -, hp⟩ := mem_support_bindK hp
      rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
    · rw [B₁.outcome_challenge_some _ dem b _ _ _ hin] at hp
      rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
  · rw [B₁.outcome_dec _ dem b cB _ _ hin (kem.decaps keys.2)
      (fun c₁ h => by rw [KEM.ChallengeCCA.Game.outcome_dec, if_neg h])] at hp
    rw [((Finsupp.mem_support_single _ _ _).mp hp).1]

/-- **`IND-CCA^KEM(b')` is initialized once `B₁ b` is**: an invariant of
`B₁ b • IND-CCA^KEM(b')`. -/
lemma B₁.initKEM_pres (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (b b' : Bool)
    (s : Option (Option (C₁ × C₂)) ×
      (Option ((PK × SK) × K × (PK → C₁ × K)) × Unit × Unit × Unit) × Unit)
    (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o) (hs : s.2.1.1 = none → s.1 = none) (p)
    (hp : p ∈ ((B₁.freshStep dem b (KEM.ChallengeCCA.Game.freshStep kem b')).outcome s x).support) :
    p.1.2.1.1 = none → p.1.1 = none := by
  rcases s with ⟨cB, ⟨_ | ⟨keys, k₁, e⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩
  · obtain rfl : cB = none := hs rfl
    rw [B₁.outcome_initKEM] at hp
    obtain ⟨keys, -, hp⟩ := mem_support_bindK hp
    obtain ⟨k₁, -, hp⟩ := mem_support_bindK hp
    obtain ⟨e, -, hp⟩ := mem_support_bindK hp
    simp [B₁.mem_support_outcome_KEM kem dem b b' none keys k₁ e x p hp]
  · simp [B₁.mem_support_outcome_KEM kem dem b b' cB keys k₁ e x p hp]

end B₁KEM

/-! ### `B₂` -/

section B₂

omit [DecidableEq SK] [DecidableEq K] [DecidableEq M] [Nonempty K]

/-- The challenge ciphertext of a reply of `IND-CCA^DEM(b)`. -/
def ChallengeLeftRight.challengeOf : (Σ i, ChallengeLeftRight.Output M C₂ i) → Option C₂
  | ⟨.challenge, c⟩ => c
  | ⟨.dec, _⟩ => none

/-- The decryption of a reply of `IND-CCA^DEM(b)`. -/
def ChallengeLeftRight.decryptionOf : (Σ i, ChallengeLeftRight.Output M C₂ i) → Option M
  | ⟨.dec, m⟩ => m
  | ⟨.challenge, _⟩ => none

variable {R : Type} (stepR : ProbStep R ChallengeLeftRight.Port (ChallengeLeftRight.Input M C₂)
  (ChallengeLeftRight.Output M C₂))

/-- **`B₂` on the public key.** -/
lemma B₂.outcome_publicKey (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (keys : PK × SK) (e : PK → C₁ × K) (cs : Option (C₁ × C₂)) (r : R) :
    (B₂.freshStep kem dem stepR).outcome (some (keys, e, cs), (r, ((), ()))) ⟨.publicKey, ()⟩ =
      Finsupp.single ((some (keys, e, cs), (r, ((), ()))),
        (⟨.publicKey, keys.1⟩ : Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (keys, e, cs), keys.1)) (by simp [B₂.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **`B₂` on a challenge**: `c* = (c₁*, c₂*)` for the challenge `c₂*` of the DEM game. -/
lemma B₂.outcome_challenge (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (keys : PK × SK) (e : PK → C₁ × K) (cs : Option (C₁ × C₂)) (r : R) (m₀ m₁ : M) :
    (B₂.freshStep kem dem stepR).outcome (some (keys, e, cs), (r, ((), ())))
        ⟨.challenge, (m₀, m₁)⟩ =
      bindK (stepR.outcome r ⟨.challenge, (m₀, m₁)⟩) fun p =>
        Finsupp.single ((some (keys, e,
            ((ChallengeLeftRight.challengeOf p.2).map fun c₂ => ((e keys.1).1, c₂)).or cs),
            (p.1, ((), ()))),
          (⟨.challenge, (ChallengeLeftRight.challengeOf p.2).map fun c₂ => ((e keys.1).1, c₂)⟩ :
            Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val]
  rw [show B₂.bound M C₂ kem dem = 2 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl .challenge, (m₀, m₁)⟩)
      (by simp [B₂.body, callProg]),
    ProbStep.outcome_parallel_inl, bindK_fTransform, fTransform_bindK]
  refine bindK_congr fun p hp => ?_
  obtain ⟨r', j, y⟩ := p
  obtain ⟨y', hy⟩ := Program.mem_support_outcome hp
  cases hy
  cases y' with
  | none =>
    rw [Function.comp_apply, Program.probInvoke_inl (a := (some (keys, e, cs), none))
      (by simp [B₂.body, callProg, returnProg, ProbStep.inlReply])]
    simp [fTransform, ProbStep.tagged, ChallengeLeftRight.challengeOf]
  | some c₂ =>
    rw [Function.comp_apply, Program.probInvoke_inl
      (a := (some (keys, e, some ((e keys.1).1, c₂)), some ((e keys.1).1, c₂)))
      (by simp [B₂.body, callProg, returnProg, ProbStep.inlReply])]
    simp [fTransform, ProbStep.tagged, ChallengeLeftRight.challengeOf]

/-- **`B₂` on a decryption under `c₁*`**: the decryption of the DEM game. -/
lemma B₂.outcome_dec_challenge (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (keys : PK × SK) (e : PK → C₁ × K) (cs : Option (C₁ × C₂)) (r : R) (c : C₁ × C₂)
    (h₁ : cs ≠ some c) (h₂ : c.1 = (e keys.1).1) :
    (B₂.freshStep kem dem stepR).outcome (some (keys, e, cs), (r, ((), ()))) ⟨.dec, c⟩ =
      bindK (stepR.outcome r ⟨.dec, c.2⟩) fun p =>
        Finsupp.single ((some (keys, e, cs), (p.1, ((), ()))),
          (⟨.dec, ChallengeLeftRight.decryptionOf p.2⟩ :
            Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val]
  rw [show B₂.bound M C₂ kem dem = 2 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl .dec, c.2⟩)
      (by simp [B₂.body, callProg, h₁, h₂]),
    ProbStep.outcome_parallel_inl, bindK_fTransform, fTransform_bindK]
  refine bindK_congr fun p hp => ?_
  obtain ⟨r', j, y⟩ := p
  obtain ⟨y', hy⟩ := Program.mem_support_outcome hp
  cases hy
  dsimp only [Function.comp_apply]
  rw [Program.probInvoke_inl (o := PKEChallenge.Port.dec) (a := (some (keys, e, cs), y'))
    (by simp [B₂.body, callProg, returnProg, ProbStep.inlReply, h₁, h₂])]
  simp [fTransform, ProbStep.tagged, ChallengeLeftRight.decryptionOf]

/-- **`B₂` on any other decryption**: `⊥` on `c*`, otherwise `PKE.Dec(sk, c)`. -/
lemma B₂.outcome_dec (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (keys : PK × SK) (e : PK → C₁ × K) (cs : Option (C₁ × C₂)) (r : R) (c : C₁ × C₂)
    (h : cs = some c ∨ c.1 ≠ (e keys.1).1) :
    (B₂.freshStep kem dem stepR).outcome (some (keys, e, cs), (r, ((), ()))) ⟨.dec, c⟩ =
      Finsupp.single ((some (keys, e, cs), (r, ((), ()))),
        (⟨.dec, if cs = some c then none else (kem.decaps keys.2 c.1).bind fun k => dem.dec k c.2⟩ :
          Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (keys, e, cs),
      if cs = some c then none else (kem.decaps keys.2 c.1).bind fun k => dem.dec k c.2))
      (by rcases h with h | h <;> by_cases h₁ : cs = some c <;> simp_all [B₂.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **`B₂` initializes at its first query**: the keys and the encapsulations are sampled. -/
lemma B₂.outcome_none (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (r : R)
    (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o) :
    (B₂.freshStep kem dem stepR).outcome (none, (r, ((), ()))) x =
      bindK kem.gen.1 fun keys => bindK kem.encapsulations.1 fun e =>
        (B₂.freshStep kem dem stepR).outcome (some (keys, e, none), (r, ((), ()))) x := by
  obtain ⟨o, u⟩ := x
  conv_lhs =>
    rw [ProbStep.outcome, Program.probCombine_val, show B₂.bound M C₂ kem dem = 2 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inr (.inl ()), ()⟩)
        (by cases o <;> simp [B₂.body, callProg]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun keys _ => ?_
  conv_lhs =>
    rw [Program.probInvoke_succ_inr (q := ⟨.inr (.inr ()), ()⟩)
        (by cases o <;> simp [B₂.body, callProg, ProbStep.inrReply, ProbStep.inlReply]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun e _ => ?_
  cases o
  · obtain ⟨⟩ := u
    rw [B₂.outcome_publicKey, Program.probInvoke_inl (a := (some (keys, e, none), keys.1))
      (by simp [B₂.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply])]
    simp [fTransform, ProbStep.tagged]
  · obtain ⟨m₀, m₁⟩ := u
    rw [B₂.outcome_challenge, Program.probInvoke_succ_inr (q := ⟨.inl .challenge, (m₀, m₁)⟩)
        (by simp [B₂.body, callProg, ProbStep.inlReply, ProbStep.inrReply]),
      ProbStep.outcome_parallel_inl, bindK_fTransform, fTransform_bindK]
    refine bindK_congr fun p hp => ?_
    obtain ⟨r', j, y⟩ := p
    obtain ⟨y', hy⟩ := Program.mem_support_outcome hp
    cases hy
    dsimp only [Function.comp_apply]
    cases y' with
    | none =>
      rw [Program.probInvoke_inl (o := PKEChallenge.Port.challenge)
        (a := (some (keys, e, none), none))
        (by simp [B₂.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply])]
      simp [fTransform, ProbStep.tagged, ChallengeLeftRight.challengeOf]
    | some c₂ =>
      rw [Program.probInvoke_inl (o := PKEChallenge.Port.challenge)
        (a := (some (keys, e, some ((e keys.1).1, c₂)), some ((e keys.1).1, c₂)))
        (by simp [B₂.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply])]
      simp [fTransform, ProbStep.tagged, ChallengeLeftRight.challengeOf]
  · by_cases h₂ : u.1 = (e keys.1).1
    · rw [B₂.outcome_dec_challenge _ kem dem keys e none r u (by simp) h₂,
        Program.probInvoke_succ_inr (q := ⟨.inl .dec, u.2⟩)
          (by simp [B₂.body, callProg, ProbStep.inlReply, ProbStep.inrReply, h₂]),
        ProbStep.outcome_parallel_inl, bindK_fTransform, fTransform_bindK]
      refine bindK_congr fun p hp => ?_
      obtain ⟨r', j, y⟩ := p
      obtain ⟨y', hy⟩ := Program.mem_support_outcome hp
      cases hy
      dsimp only [Function.comp_apply]
      rw [Program.probInvoke_inl (o := PKEChallenge.Port.dec) (a := (some (keys, e, none), y'))
        (by simp [B₂.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply, h₂])]
      simp [fTransform, ProbStep.tagged, ChallengeLeftRight.decryptionOf]
    · rw [B₂.outcome_dec _ kem dem keys e none r u (Or.inr h₂),
        Program.probInvoke_inl (a := (some (keys, e, none),
          (kem.decaps keys.2 u.1).bind fun k => dem.dec k u.2))
          (by simp [B₂.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply, h₂])]
      simp [fTransform, ProbStep.tagged]

end B₂

/-! ### `B₂ • IND-CCA^DEM(b)` -/

section B₂DEM

omit [DecidableEq SK]

/-- The fresh-sampling step of `B₂ • IND-CCA^DEM(b)`. -/
noncomputable abbrev B₂.freshStepDEM (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b : Bool) :
    ProbStep (Option ((PK × SK) × (PK → C₁ × K) × Option (C₁ × C₂)) ×
        ((Option (K × Option C₂) × Unit × Unit) × Unit × Unit))
      PKEChallenge.Port (PKEChallenge.Input M (C₁ × C₂)) (PKEChallenge.Output PK M (C₁ × C₂)) :=
  B₂.freshStep kem dem (DEM.ChallengeCCA.Game.freshStep dem b)

/-- **`B₂` initializes at its first query**, before `IND-CCA^DEM(b)`. -/
lemma B₂.outcome_initDEM (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (b : Bool)
    (d : Option (K × Option C₂)) (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o) :
    (B₂.freshStepDEM kem dem b).outcome (none, ((d, ((), ())), ((), ()))) x =
      bindK kem.gen.1 fun keys => bindK kem.encapsulations.1 fun e =>
        (B₂.freshStepDEM kem dem b).outcome (some (keys, e, none), ((d, ((), ())), ((), ()))) x :=
  B₂.outcome_none _ kem dem _ x

/-- **`B₂ • IND-CCA^DEM(b)` on the public key.** -/
lemma B₂.outcome_publicKey_DEM (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b : Bool) (keys : PK × SK) (e : PK → C₁ × K) (cs : Option (C₁ × C₂))
    (d : Option (K × Option C₂)) :
    (B₂.freshStepDEM kem dem b).outcome
        (some (keys, e, cs), ((d, ((), ())), ((), ()))) ⟨.publicKey, ()⟩ =
      Finsupp.single ((some (keys, e, cs), ((d, ((), ())), ((), ()))),
        (⟨.publicKey, keys.1⟩ : Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 :=
  B₂.outcome_publicKey _ kem dem keys e cs _

/-- **The first challenge of `B₂` initializes `IND-CCA^DEM(b)`**: `k ← K` and
`c* = (c₁*, Enc(k, m_b))`. -/
lemma B₂.outcome_challenge_DEM_none (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b : Bool) (keys : PK × SK) (e : PK → C₁ × K) (m₀ m₁ : M) :
    (B₂.freshStepDEM kem dem b).outcome
        (some (keys, e, none), ((none, ((), ())), ((), ()))) ⟨.challenge, (m₀, m₁)⟩ =
      bindK (𝒰[K]).1 fun k => bindK dem.encryptions.1 fun E =>
        Finsupp.single ((some (keys, e, some ((e keys.1).1, E (k, if b then m₁ else m₀))),
            ((some (k, some (E (k, if b then m₁ else m₀))), ((), ())), ((), ()))),
          (⟨.challenge, some ((e keys.1).1, E (k, if b then m₁ else m₀))⟩ :
            Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [B₂.outcome_challenge, DEM.ChallengeCCA.Game.outcome_challenge_none]
  simp only [bindK_bindK, bindK_single, one_smul]
  rfl

/-- **The first challenge of `B₂` on an initialized `IND-CCA^DEM(b)`**:
`c* = (c₁*, Enc(k, m_b))`. -/
lemma B₂.outcome_challenge_DEM (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b : Bool) (keys : PK × SK) (e : PK → C₁ × K) (cs : Option (C₁ × C₂)) (k : K)
    (m₀ m₁ : M) :
    (B₂.freshStepDEM kem dem b).outcome
        (some (keys, e, cs), ((some (k, none), ((), ())), ((), ()))) ⟨.challenge, (m₀, m₁)⟩ =
      bindK dem.encryptions.1 fun E =>
        Finsupp.single ((some (keys, e, some ((e keys.1).1, E (k, if b then m₁ else m₀))),
            ((some (k, some (E (k, if b then m₁ else m₀))), ((), ())), ((), ()))),
          (⟨.challenge, some ((e keys.1).1, E (k, if b then m₁ else m₀))⟩ :
            Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [B₂.outcome_challenge, DEM.ChallengeCCA.Game.outcome_challenge]
  simp only [bindK_bindK, bindK_single, one_smul]
  rfl

/-- **A later challenge of `B₂`**: the DEM game refuses it. -/
lemma B₂.outcome_challenge_DEM_some (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b : Bool) (keys : PK × SK) (e : PK → C₁ × K) (cs : Option (C₁ × C₂)) (k : K)
    (c₂ : C₂) (m₀ m₁ : M) :
    (B₂.freshStepDEM kem dem b).outcome
        (some (keys, e, cs), ((some (k, some c₂), ((), ())), ((), ()))) ⟨.challenge, (m₀, m₁)⟩ =
      Finsupp.single ((some (keys, e, cs), ((some (k, some c₂), ((), ())), ((), ()))),
        (⟨.challenge, none⟩ : Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [B₂.outcome_challenge, DEM.ChallengeCCA.Game.outcome_challenge_some, bindK_single, one_smul]
  rfl

/-- **A decryption of `B₂` under `c₁*` initializes `IND-CCA^DEM(b)`**: `k ← K`, then
`Dec(k, c₂)`. -/
lemma B₂.outcome_dec_DEM_none (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b : Bool) (keys : PK × SK) (e : PK → C₁ × K) (cs : Option (C₁ × C₂)) (c : C₁ × C₂)
    (h₁ : cs ≠ some c) (h₂ : c.1 = (e keys.1).1) :
    (B₂.freshStepDEM kem dem b).outcome
        (some (keys, e, cs), ((none, ((), ())), ((), ()))) ⟨.dec, c⟩ =
      bindK (𝒰[K]).1 fun k =>
        Finsupp.single ((some (keys, e, cs), ((some (k, none), ((), ())), ((), ()))),
          (⟨.dec, dem.dec k c.2⟩ : Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [B₂.outcome_dec_challenge _ kem dem keys e cs _ c h₁ h₂,
    DEM.ChallengeCCA.Game.outcome_dec_none]
  simp only [bindK_bindK, bindK_single, one_smul]
  rfl

/-- **A decryption of `B₂` under `c₁*` on an initialized `IND-CCA^DEM(b)`.** -/
lemma B₂.outcome_dec_DEM (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b : Bool) (keys : PK × SK) (e : PK → C₁ × K) (cs : Option (C₁ × C₂)) (k : K)
    (cd : Option C₂) (c : C₁ × C₂) (h₁ : cs ≠ some c) (h₂ : c.1 = (e keys.1).1) :
    (B₂.freshStepDEM kem dem b).outcome
        (some (keys, e, cs), ((some (k, cd), ((), ())), ((), ()))) ⟨.dec, c⟩ =
      Finsupp.single ((some (keys, e, cs), ((some (k, cd), ((), ())), ((), ()))),
        (⟨.dec, if cd = some c.2 then none else dem.dec k c.2⟩ :
          Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  rw [B₂.outcome_dec_challenge _ kem dem keys e cs _ c h₁ h₂, DEM.ChallengeCCA.Game.outcome_dec,
    bindK_single, one_smul]
  rfl

/-- **Any other decryption of `B₂`** does not query `IND-CCA^DEM(b)`. -/
lemma B₂.outcome_dec_other (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b : Bool) (keys : PK × SK) (e : PK → C₁ × K) (cs : Option (C₁ × C₂))
    (d : Option (K × Option C₂)) (c : C₁ × C₂) (h : cs = some c ∨ c.1 ≠ (e keys.1).1) :
    (B₂.freshStepDEM kem dem b).outcome
        (some (keys, e, cs), ((d, ((), ())), ((), ()))) ⟨.dec, c⟩ =
      Finsupp.single ((some (keys, e, cs), ((d, ((), ())), ((), ()))),
        (⟨.dec, if cs = some c then none else (kem.decaps keys.2 c.1).bind fun k => dem.dec k c.2⟩ :
          Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 :=
  B₂.outcome_dec _ kem dem keys e cs _ c h

end B₂DEM

/-! ### Maps of states and kernels -/

/-- **The state of `G₁(b)` of a state of `B₁ b • IND-CCA^KEM(0)`**: `k₁` is forgotten. -/
def B₁.stateG₁ (s : Option (Option (C₁ × C₂)) ×
    (Option ((PK × SK) × K × (PK → C₁ × K)) × Unit × Unit × Unit) × Unit) :
    Option ((PK × SK) × (PK → C₁ × K) × Option (C₁ × C₂)) × Unit × Unit × Unit :=
  (s.2.1.1.map fun x => (x.1, x.2.2, s.1.getD none), ((), ((), ())))

/-- **The state of `G₂(b)` of a state of `B₁ b • IND-CCA^KEM(1)`**: `k₁` is `k*`, and the
encapsulated key is forgotten. -/
def B₁.stateG₂ (s : Option (Option (C₁ × C₂)) ×
    (Option ((PK × SK) × K × (PK → C₁ × K)) × Unit × Unit × Unit) × Unit) :
    Option ((PK × SK) × (PK → C₁ × K) × K × Option (C₁ × C₂)) × Unit × Unit × Unit × Unit :=
  (s.2.1.1.map fun x => (x.1, x.2.2, x.2.1, s.1.getD none), ((), ((), ((), ()))))

/-- **The states of `G₂(b)` of a state of `B₂ • IND-CCA^DEM(b)`**: `k*` is the key of the DEM
game, sampled afresh while the DEM game is uninitialized. -/
noncomputable def B₂.kernelG₂ (s : Option ((PK × SK) × (PK → C₁ × K) × Option (C₁ × C₂)) ×
    ((Option (K × Option C₂) × Unit × Unit) × Unit × Unit)) :
    Distribution.ProbDist (Option ((PK × SK) × (PK → C₁ × K) × K × Option (C₁ × C₂)) ×
      Unit × Unit × Unit × Unit) :=
  match s with
  | (some (keys, e, cs), ((some (k, _), _), _)) =>
    Distribution.ProbDist.single (some (keys, e, k, cs), ((), ((), ((), ()))))
  | (some (keys, e, cs), ((none, _), _)) =>
    Distribution.ProbDist.map (fun k => (some (keys, e, k, cs), ((), ((), ((), ()))))) 𝒰[K]
  | (none, _) => Distribution.ProbDist.single (none, ((), ((), ((), ()))))

/-- **The invariant of `B₂ • IND-CCA^DEM(b)`**: the DEM game is initialized after `B₂`, and the
challenge of `B₂` is `c₁*` with the challenge of the DEM game. -/
def B₂.ChallengeAgrees (s : Option ((PK × SK) × (PK → C₁ × K) × Option (C₁ × C₂)) ×
    ((Option (K × Option C₂) × Unit × Unit) × Unit × Unit)) : Prop :=
  match s with
  | (none, ((d, _), _)) => d = none
  | (some (_, _, cs), ((none, _), _)) => cs = none
  | (some (keys, e, cs), ((some (_, cd), _), _)) => cs = cd.map fun c₂ => ((e keys.1).1, c₂)

/-- **Independent encapsulations given the one under `pk`**: `ck` under `pk`, and independent
encapsulations under every other public key. -/
noncomputable def KEM.encapsulationsGiven (kem : KEM PK SK C₁ K) (pk : PK) (ck : C₁ × K) :
    Distribution.ProbDist (PK → C₁ × K) :=
  ⟨Distribution.pi (Function.update (fun pk => (kem.encaps pk).1) pk (Finsupp.single ck 1)),
    pi_isProbDist fun i => by
      by_cases h : i = pk
      · subst h
        rw [Function.update_self]
        exact isProbDist_single ck
      · rw [Function.update_of_ne h]
        exact (kem.encaps i).2⟩

omit [Fintype SK] [Fintype C₁] [Fintype K] [DecidableEq SK] [DecidableEq C₁] [DecidableEq K]
  [Nonempty K] in
/-- **The encapsulations disintegrate** at one public key. -/
lemma KEM.encapsulations_eq_bindK (kem : KEM PK SK C₁ K) (pk : PK) :
    kem.encapsulations.1 =
      bindK (kem.encaps pk).1 fun ck => (KEM.encapsulationsGiven kem pk ck).1 :=
  pi_eq_bindK_update _ pk

omit [Fintype SK] [Fintype C₁] [Fintype K] [DecidableEq SK] [DecidableEq C₁] [DecidableEq K]
  [Nonempty K] in
/-- The encapsulations given `ck` under `pk` hold `ck` under `pk`. -/
lemma KEM.apply_of_mem_support_encapsulationsGiven {kem : KEM PK SK C₁ K} {pk : PK}
    {ck : C₁ × K} {e : PK → C₁ × K} (he : e ∈ (KEM.encapsulationsGiven kem pk ck).1.support) :
    e pk = ck :=
  eq_of_mem_support_pi_update _ _ _ he

omit [Fintype C₂] [DecidableEq C₂] [Nonempty K] in
/-- **The encryption of one message under one key** is a marginal of the encryptions. -/
lemma SymmetricEncryption.bindK_encryptions {B : Type} (dem : SymmetricEncryption K M C₂)
    (k : K) (m : M) (F : C₂ → Distribution B) :
    bindK dem.encryptions.1 (fun E => F (E (k, m))) = bindK (dem.enc k m).1 F :=
  bindK_pi_apply (fun km : K × M => (dem.enc km.1 km.2).1) (fun km => (dem.enc km.1 km.2).2.2)
    (k, m) F

omit [Fintype SK] [DecidableEq SK] in
/-- **The encryption of one message under one public key** is a marginal of the encryptions. -/
lemma PublicKeyEncryption.bindK_encryptions {B C : Type} [Fintype C]
    (pke : PublicKeyEncryption PK SK M C) (pk : PK) (m : M) (F : C → Distribution B) :
    bindK pke.encryptions.1 (fun E => F (E (pk, m))) = bindK (pke.enc pk m).1 F :=
  bindK_pi_apply (fun pm : PK × M => (pke.enc pm.1 pm.2).1) (fun pm => (pke.enc pm.1 pm.2).2.2)
    (pk, m) F

omit [Fintype SK] [Fintype C₁] [Fintype K] [DecidableEq SK] [DecidableEq C₁] [DecidableEq K]
  [Nonempty K] in
/-- **The encapsulation under one public key** is a marginal of the encapsulations. -/
lemma KEM.bindK_encapsulations {B : Type} (kem : KEM PK SK C₁ K) (pk : PK)
    (F : C₁ × K → Distribution B) :
    bindK kem.encapsulations.1 (fun e => F (e pk)) = bindK (kem.encaps pk).1 F :=
  bindK_pi_apply (fun pk => (kem.encaps pk).1) (fun pk => (kem.encaps pk).2.2) pk F

/-- **The states of `G₁(b)` of a state of `IND-CCA^PKE(b)`**: the encapsulations are sampled
afresh, given the one of the challenge once there is a challenge. -/
noncomputable def PKE.ChallengeCCA.Game.kernelG₁ (kem : KEM PK SK C₁ K)
    (s : Option ((PK × SK) × Option (C₁ × C₂)) × Unit × Unit) :
    Distribution.ProbDist (Option ((PK × SK) × (PK → C₁ × K) × Option (C₁ × C₂)) ×
      Unit × Unit × Unit) :=
  match s with
  | (none, _) => Distribution.ProbDist.single (none, ((), ((), ())))
  | (some (keys, none), _) =>
    Distribution.ProbDist.map (fun e => (some (keys, e, none), ((), ((), ())))) kem.encapsulations
  | (some (keys, some c), _) =>
    match kem.decaps keys.2 c.1 with
    | some k => Distribution.ProbDist.map (fun e => (some (keys, e, some c), ((), ((), ()))))
        (KEM.encapsulationsGiven kem keys.1 (c.1, k))
    | none => Distribution.ProbDist.single (none, ((), ((), ())))

/-- **The invariant of `IND-CCA^PKE(b)`**: the keys are generated, and the challenge
encapsulates under the public key. -/
def PKE.ChallengeCCA.Game.Encapsulated (kem : KEM PK SK C₁ K)
    (s : Option ((PK × SK) × Option (C₁ × C₂)) × Unit × Unit) : Prop :=
  match s with
  | (none, _) => True
  | (some (keys, cs), _) => keys ∈ kem.gen.1.support ∧
    ∀ c, cs = some c → ∃ k, (c.1, k) ∈ (kem.encaps keys.1).1.support


/-! ### The upfront sample of the imperfect-correctness variant

`IND-CCA^PKE(b)` and `G₁(b)` are both mixtures over the keys and the encapsulations sampled once
(`Resource.sample`): `IND-CCA^PKE(b)` is the upfront game, which uses the encapsulation under `pk`
at the challenge and then forgets its key, along the kernel that samples the encapsulations while
there is no challenge; `G₁(b)` is itself from its initialized states. On a sample under which
decapsulating `c₁*` gives `k*`, the two components are one resource. -/

section Upfront

/-- **`IND-CCA^PKE(b)` of KEM + DEM with the challenge encapsulation upfront**: the state holds the
keys and the encapsulation `(c₁*, k*)` of the challenge until the challenge, and the challenge
`c* = (c₁*, DEM.Enc(k*, m_b))` after it, without `k*`. -/
noncomputable def PKE.ChallengeCCA.Game.upfrontStep (kem : KEM PK SK C₁ K)
    (dem : SymmetricEncryption K M C₂) (b : Bool) :
    ProbStep ((PK × SK) × ((C₁ × K) ⊕ (C₁ × C₂))) PKEChallenge.Port
      (PKEChallenge.Input M (C₁ × C₂)) (PKEChallenge.Output PK M (C₁ × C₂))
  | s, .publicKey, () => Distribution.ProbDist.single (s, s.1.1)
  | (keys, .inl ck), .challenge, (m₀, m₁) =>
    Distribution.ProbDist.map (fun c₂ => ((keys, .inr (ck.1, c₂)), some (ck.1, c₂)))
      (dem.enc ck.2 (if b then m₁ else m₀))
  | (keys, .inr c), .challenge, _ => Distribution.ProbDist.single ((keys, .inr c), none)
  | (keys, t), .dec, c => Distribution.ProbDist.single ((keys, t),
      if t = .inr c then none else (kem.decaps keys.2 c.1).bind fun k => dem.dec k c.2)

omit [Fintype SK] [Fintype K] [DecidableEq PK] [DecidableEq SK] [DecidableEq M] [Nonempty K] in
/-- **The upfront `IND-CCA^PKE(b)` on the public key.** -/
lemma PKE.ChallengeCCA.Game.upfront_outcome_publicKey (kem : KEM PK SK C₁ K)
    (dem : SymmetricEncryption K M C₂) (b : Bool) (s : (PK × SK) × ((C₁ × K) ⊕ (C₁ × C₂))) :
    (PKE.ChallengeCCA.Game.upfrontStep kem dem b).outcome s ⟨.publicKey, ()⟩ =
      Finsupp.single (s, (⟨.publicKey, s.1.1⟩ : Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  simp [ProbStep.outcome, PKE.ChallengeCCA.Game.upfrontStep, Distribution.ProbDist.single,
    fTransform_single, ProbStep.tagged]

omit [Fintype SK] [Fintype K] [DecidableEq PK] [DecidableEq SK] [DecidableEq M] [Nonempty K] in
/-- **The upfront `IND-CCA^PKE(b)` on the first challenge**: `c* = (c₁*, DEM.Enc(k*, m_b))`. -/
lemma PKE.ChallengeCCA.Game.upfront_outcome_challenge (kem : KEM PK SK C₁ K)
    (dem : SymmetricEncryption K M C₂) (b : Bool) (keys : PK × SK) (ck : C₁ × K) (m₀ m₁ : M) :
    (PKE.ChallengeCCA.Game.upfrontStep kem dem b).outcome (keys, .inl ck) ⟨.challenge, (m₀, m₁)⟩ =
      bindK (dem.enc ck.2 (if b then m₁ else m₀)).1 fun c₂ =>
        Finsupp.single ((keys, .inr (ck.1, c₂)),
          (⟨.challenge, some (ck.1, c₂)⟩ : Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  simp only [ProbStep.outcome, PKE.ChallengeCCA.Game.upfrontStep, Distribution.ProbDist.map]
  rw [fTransform_fTransform, fTransform_eq_bindK]
  rfl

omit [Fintype SK] [Fintype K] [DecidableEq PK] [DecidableEq SK] [DecidableEq M] [Nonempty K] in
/-- **The upfront `IND-CCA^PKE(b)` on a later challenge**: `⊥`. -/
lemma PKE.ChallengeCCA.Game.upfront_outcome_challenge_inr (kem : KEM PK SK C₁ K)
    (dem : SymmetricEncryption K M C₂) (b : Bool) (keys : PK × SK) (c : C₁ × C₂) (m₀ m₁ : M) :
    (PKE.ChallengeCCA.Game.upfrontStep kem dem b).outcome (keys, .inr c) ⟨.challenge, (m₀, m₁)⟩ =
      Finsupp.single ((keys, .inr c),
        (⟨.challenge, none⟩ : Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  simp [ProbStep.outcome, PKE.ChallengeCCA.Game.upfrontStep, Distribution.ProbDist.single,
    fTransform_single, ProbStep.tagged]

omit [Fintype SK] [Fintype K] [DecidableEq PK] [DecidableEq SK] [DecidableEq M] [Nonempty K] in
/-- **The upfront `IND-CCA^PKE(b)` on a decryption**: `⊥` on `c*`, otherwise `PKE.Dec(sk, c)`. -/
lemma PKE.ChallengeCCA.Game.upfront_outcome_dec (kem : KEM PK SK C₁ K)
    (dem : SymmetricEncryption K M C₂) (b : Bool) (keys : PK × SK)
    (t : (C₁ × K) ⊕ (C₁ × C₂)) (c : C₁ × C₂) :
    (PKE.ChallengeCCA.Game.upfrontStep kem dem b).outcome (keys, t) ⟨.dec, c⟩ =
      Finsupp.single ((keys, t), (⟨.dec, if t = .inr c then none else
        (kem.decaps keys.2 c.1).bind fun k => dem.dec k c.2⟩ :
          Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 := by
  simp [ProbStep.outcome, PKE.ChallengeCCA.Game.upfrontStep, Distribution.ProbDist.single,
    fTransform_single, ProbStep.tagged]

/-- **The states of the upfront `IND-CCA^PKE(b)` of a state of `IND-CCA^PKE(b)`**: the keys and
the encapsulations sampled while they are not, and the challenge kept once there is one. -/
noncomputable def PKE.ChallengeCCA.Game.kernelUpfront (kem : KEM PK SK C₁ K) :
    Option ((PK × SK) × Option (C₁ × C₂)) × Unit × Unit →
      Distribution.ProbDist ((PK × SK) × ((C₁ × K) ⊕ (C₁ × C₂)))
  | (none, _) => Distribution.ProbDist.map (fun z => (z.1, .inl (z.2 z.1.1)))
      (Distribution.prodProbDist kem.gen kem.encapsulations)
  | (some (keys, none), _) =>
    Distribution.ProbDist.map (fun e => (keys, .inl (e keys.1))) kem.encapsulations
  | (some (keys, some c), _) => Distribution.ProbDist.single (keys, .inr c)

omit [DecidableEq SK] [Nonempty K] in
/-- **`IND-CCA^PKE(b)` as a mixture over the upfront sample**: the keys and the encapsulations
sampled once, and the upfront `IND-CCA^PKE(b)` at the keys and the encapsulation under `pk`. -/
lemma PKE.ChallengeCCA.Game.eq_sample (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b : Bool) {q : ℕ} :
    (PKE.ChallengeCCA.Game (scheme kem dem) b (budget := q) :
        Resource (PKEChallenge PK M (C₁ × C₂) q)) =
      Resource.sample (Distribution.prodProbDist kem.gen kem.encapsulations).1 fun z =>
        Resource.ofProbAutomaton _ (PKE.ChallengeCCA.Game.upfrontStep kem dem b)
          (Distribution.ProbDist.single (z.1, .inl (z.2 z.1.1))) := by
  -- Before the challenge, the challenge encapsulation is sampled by the kernel.
  have hI : ∀ (keys : PK × SK) (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o),
      ProbStep.SimulatesAt (PKE.ChallengeCCA.Game.freshStep (scheme kem dem) b)
        (PKE.ChallengeCCA.Game.upfrontStep kem dem b) (PKE.ChallengeCCA.Game.kernelUpfront kem)
        (some (keys, none), ((), ())) x := by
    intro keys ⟨o, u⟩
    unfold ProbStep.SimulatesAt
    dsimp only [PKE.ChallengeCCA.Game.kernelUpfront, Distribution.ProbDist.map]
    rw [bindK_fTransform]
    cases o
    · obtain ⟨⟩ := u
      rw [PKE.ChallengeCCA.Game.outcome_publicKey, bindK_single, one_smul]
      dsimp only [PKE.ChallengeCCA.Game.kernelUpfront, Distribution.ProbDist.map]
      rw [fTransform_fTransform, fTransform_eq_bindK]
      refine bindK_congr fun e _ => ?_
      exact PKE.ChallengeCCA.Game.upfront_outcome_publicKey kem dem b _
    · -- The challenge encapsulation is the encapsulation of the challenge encryption.
      obtain ⟨m₀, m₁⟩ := u
      rw [PKE.ChallengeCCA.Game.outcome_challenge, bindK_bindK]
      simp only [bindK_single, one_smul, Distribution.ProbDist.single, fTransform_single,
        Function.comp_def,
        PKE.ChallengeCCA.Game.upfront_outcome_challenge]
      rw [PublicKeyEncryption.bindK_encryptions (scheme kem dem) keys.1 (if b then m₁ else m₀)
        (fun c => Finsupp.single ((keys, (Sum.inr c : (C₁ × K) ⊕ (C₁ × C₂))),
          (⟨.challenge, some c⟩ : Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1)]
      dsimp only [scheme]
      rw [Distribution.ProbDist.bind_val, bindK_bindK]
      rw [KEM.bindK_encapsulations kem keys.1 (fun ck => bindK (dem.enc ck.2
        (if b then m₁ else m₀)).1 fun c₂ =>
          Finsupp.single ((keys, (Sum.inr (ck.1, c₂) : (C₁ × K) ⊕ (C₁ × C₂))),
            (⟨.challenge, some (ck.1, c₂)⟩ : Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1)]
      refine bindK_congr fun ck _ => ?_
      rw [show (Distribution.ProbDist.map (fun c₂ => (ck.1, c₂)) (dem.enc ck.2
        (if b then m₁ else m₀))).1 = fTransform (fun c₂ => (ck.1, c₂))
          (dem.enc ck.2 (if b then m₁ else m₀)).1 from rfl, bindK_fTransform]
      rfl
    · rw [PKE.ChallengeCCA.Game.outcome_dec, bindK_single, one_smul]
      dsimp only [PKE.ChallengeCCA.Game.kernelUpfront, Distribution.ProbDist.map]
      rw [fTransform_fTransform, fTransform_eq_bindK]
      refine bindK_congr fun e _ => ?_
      rw [Function.comp_apply, PKE.ChallengeCCA.Game.upfront_outcome_dec]
      simp [scheme]
  -- After the challenge, the ciphertext is kept.
  have hII : ∀ (keys : PK × SK) (c : C₁ × C₂) (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o),
      ProbStep.SimulatesAt (PKE.ChallengeCCA.Game.freshStep (scheme kem dem) b)
        (PKE.ChallengeCCA.Game.upfrontStep kem dem b) (PKE.ChallengeCCA.Game.kernelUpfront kem)
        (some (keys, some c), ((), ())) x := by
    intro keys c ⟨o, u⟩
    unfold ProbStep.SimulatesAt
    dsimp only [PKE.ChallengeCCA.Game.kernelUpfront, Distribution.ProbDist.single]
    rw [bindK_single, one_smul]
    cases o
    · obtain ⟨⟩ := u
      rw [PKE.ChallengeCCA.Game.outcome_publicKey, bindK_single, one_smul,
        PKE.ChallengeCCA.Game.upfront_outcome_publicKey]
      simp [fTransform_single]
    · obtain ⟨m₀, m₁⟩ := u
      rw [PKE.ChallengeCCA.Game.outcome_challenge_some, bindK_single, one_smul,
        PKE.ChallengeCCA.Game.upfront_outcome_challenge_inr]
      simp [fTransform_single]
    · rw [PKE.ChallengeCCA.Game.outcome_dec, bindK_single, one_smul,
        PKE.ChallengeCCA.Game.upfront_outcome_dec]
      simp [fTransform_single, scheme]
  rw [← Interface.Resource.ofProbAutomaton_fTransform]
  refine (PKE.ChallengeCCA.Game.freshSampling (scheme kem dem) b q).eq_fresh.trans ?_
  refine Interface.Resource.ofProbAutomaton_eq_of_simulation _ _ _ _
    (PKE.ChallengeCCA.Game.kernelUpfront kem) (fun _ _ => True) (fun _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial) ?_ ?_ <;>
    dsimp only [PKE.ChallengeCCA.Game.freshSampling, FreshSampling.ofProgram,
      FreshSampling.parallel, FreshSampling.source, Distribution.ProbDist.single]
  · rintro xs ⟨_ | ⟨keys, _ | c⟩, ⟨⟩, ⟨⟩⟩ x - -
    · -- The keys are generated, then the challenge encapsulation is sampled by the kernel.
      unfold ProbStep.SimulatesAt
      rw [PKE.ChallengeCCA.Game.outcome_none, bindK_bindK]
      refine Eq.trans ?_ (bindK_congr fun keys _ => hI keys x)
      dsimp only [PKE.ChallengeCCA.Game.kernelUpfront, Distribution.ProbDist.map,
        Distribution.prodProbDist_val]
      rw [bindK_fTransform, prod_eq_bindK, bindK_bindK]
      refine bindK_congr fun keys _ => ?_
      rw [bindK_fTransform, bindK_fTransform]
      rfl
    · exact hI keys x
    · exact hII keys c x
  · rw [bindK_single, one_smul]
    rfl

omit [DecidableEq SK] [Nonempty K] in
/-- `G₁(b)` is initialized after each step. -/
lemma G₁.isSome_of_mem_support_outcome (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (b : Bool) (s : Option ((PK × SK) × (PK → C₁ × K) × Option (C₁ × C₂)) × Unit × Unit × Unit)
    (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o) (p)
    (hp : p ∈ ((G₁.freshStep kem dem b).outcome s x).support) : p.1.1.isSome := by
  have hsome : ∀ (keys : PK × SK) (e : PK → C₁ × K) (cs : Option (C₁ × C₂)) p,
      p ∈ ((G₁.freshStep kem dem b).outcome (some (keys, e, cs), ((), ((), ()))) x).support →
        p.1.1.isSome := by
    intro keys e cs p hp
    obtain ⟨o, u⟩ := x
    cases o
    · obtain ⟨⟩ := u
      rw [G₁.outcome_publicKey] at hp
      rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
      rfl
    · obtain ⟨m₀, m₁⟩ := u
      rcases cs with _ | c
      · rw [G₁.outcome_challenge] at hp
        obtain ⟨E, -, hp⟩ := mem_support_bindK hp
        rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
        rfl
      · rw [G₁.outcome_challenge_some] at hp
        rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
        rfl
    · rw [G₁.outcome_dec] at hp
      rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
      rfl
  rcases s with ⟨_ | ⟨keys, e, cs⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
  · rw [G₁.outcome_none] at hp
    obtain ⟨keys, -, hp⟩ := mem_support_bindK hp
    obtain ⟨e, -, hp⟩ := mem_support_bindK hp
    exact hsome keys e none p hp
  · exact hsome keys e cs p hp

omit [DecidableEq SK] [Nonempty K] in
/-- **`G₁(b)` as a mixture over the upfront sample**: the keys and the encapsulations sampled
once, and `G₁(b)` from them. -/
lemma G₁.eq_sample (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (b : Bool) {q : ℕ} :
    G₁ kem dem b (budget := q) =
      Resource.sample (Distribution.prodProbDist kem.gen kem.encapsulations).1 fun z =>
        Resource.ofProbAutomaton (PKEChallenge PK M (C₁ × C₂) q) (G₁.freshStep kem dem b)
          (Distribution.ProbDist.single (some (z.1, z.2, none), ((), ((), ())))) := by
  rw [← Interface.Resource.ofProbAutomaton_fTransform]
  refine (G₁.freshSampling kem dem b q).eq_fresh.trans ?_
  -- The initial state is the mixture of the initialized states.
  let κ : Option ((PK × SK) × (PK → C₁ × K) × Option (C₁ × C₂)) × Unit × Unit × Unit →
      Distribution.ProbDist (Option ((PK × SK) × (PK → C₁ × K) × Option (C₁ × C₂)) ×
        Unit × Unit × Unit) := fun s => match s.1 with
    | none => ⟨fTransform (fun z => (some (z.1, z.2, none), ((), ((), ()))))
        (Distribution.prodProbDist kem.gen kem.encapsulations).1, fTransform_isProbDist _
          (Distribution.prodProbDist kem.gen kem.encapsulations).2⟩
    | some _ => Distribution.ProbDist.single s
  -- After a step, the state is initialized.
  have hstep : ∀ s x, bindK ((G₁.freshStep kem dem b).outcome s x)
      (fun p => fTransform (fun s₂ => (s₂, p.2)) (κ p.1).1) =
        (G₁.freshStep kem dem b).outcome s x := by
    intro s x
    refine (bindK_congr fun p hp => ?_).trans (bindK_single_one _)
    obtain ⟨⟨_ | t, u⟩, y⟩ := p
    · exact absurd (G₁.isSome_of_mem_support_outcome kem dem b s x _ hp) (by simp)
    · simp [κ, Distribution.ProbDist.single, fTransform_single]
  refine Interface.Resource.ofProbAutomaton_eq_of_simulation _ _ _ _ κ (fun _ _ => True)
    (fun _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) ?_ ?_ <;>
    dsimp only [G₁.freshSampling, FreshSampling.ofProgram, FreshSampling.parallel,
      FreshSampling.source, Distribution.ProbDist.single]
  · rintro xs ⟨_ | t, ⟨⟩, ⟨⟩, ⟨⟩⟩ x - -
    · unfold ProbStep.SimulatesAt
      rw [hstep, G₁.outcome_none]
      dsimp only [κ, Distribution.prodProbDist_val]
      rw [bindK_fTransform, prod_eq_bindK, bindK_bindK]
      refine bindK_congr fun keys _ => ?_
      rw [bindK_fTransform]
      rfl
    · unfold ProbStep.SimulatesAt
      rw [hstep]
      simp [κ, Distribution.ProbDist.single]
  · rw [bindK_single, one_smul]

/-- **The state of the upfront `IND-CCA^PKE(b)` of a state of `G₁(b)`** from the keys and the
encapsulations `z`: the encapsulation under `pk` until the challenge, and the challenge after. -/
def G₁.stateUpfront (z : (PK × SK) × (PK → C₁ × K))
    (s : Option ((PK × SK) × (PK → C₁ × K) × Option (C₁ × C₂)) × Unit × Unit × Unit) :
    (PK × SK) × ((C₁ × K) ⊕ (C₁ × C₂)) :=
  (z.1, match s.1 with
    | some (_, _, some c) => .inr c
    | _ => .inl (z.2 z.1.1))

omit [DecidableEq SK] [Nonempty K] in
/-- **`G₁(b)` is `IND-CCA^PKE(b)` on a good sample**: from keys and encapsulations under which
decapsulating `c₁*` gives `k*`, `G₁(b)` and the upfront `IND-CCA^PKE(b)` are one resource. -/
lemma G₁.eq_upfront (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (b : Bool)
    {q : ℕ} (z : (PK × SK) × (PK → C₁ × K))
    (good : kem.decaps z.1.2 (z.2 z.1.1).1 = some (z.2 z.1.1).2) :
    Resource.ofProbAutomaton (PKEChallenge PK M (C₁ × C₂) q) (G₁.freshStep kem dem b)
        (Distribution.ProbDist.single (some (z.1, z.2, none), ((), ((), ())))) =
      Resource.ofProbAutomaton _ (PKE.ChallengeCCA.Game.upfrontStep kem dem b)
        (Distribution.ProbDist.single (z.1, .inl (z.2 z.1.1))) := by
  obtain ⟨keys, e⟩ := z
  refine Interface.Resource.ofProbAutomaton_eq_of_mapOn _ _ _ _ (G₁.stateUpfront (keys, e))
    (fun s => ∃ cs, s = (some (keys, e, cs), ((), ((), ()))) ∧
      ∀ c, cs = some c → c.1 = (e keys.1).1) ?_ ?_ ?_ ?_
  · intro s hs
    rw [((Finsupp.mem_support_single _ _ _).mp hs).1]
    exact ⟨none, rfl, fun c hc => absurd hc (by simp)⟩
  · rintro s ⟨o, u⟩ ⟨cs, rfl, hcs⟩ p hp
    cases o
    · rw [G₁.outcome_publicKey] at hp
      rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
      exact ⟨cs, rfl, hcs⟩
    · obtain ⟨m₀, m₁⟩ := u
      rcases cs with _ | c
      · rw [G₁.outcome_challenge] at hp
        obtain ⟨E, -, hp⟩ := mem_support_bindK hp
        rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
        exact ⟨_, rfl, fun c hc => by rw [← Option.some_injective _ hc]⟩
      · rw [G₁.outcome_challenge_some] at hp
        rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
        exact ⟨some c, rfl, hcs⟩
    · rw [G₁.outcome_dec] at hp
      rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
      exact ⟨cs, rfl, hcs⟩
  · rintro s ⟨o, u⟩ ⟨cs, rfl, hcs⟩
    cases o
    · obtain ⟨⟩ := u
      rw [G₁.outcome_publicKey, PKE.ChallengeCCA.Game.upfront_outcome_publicKey, fTransform_single]
      rfl
    · obtain ⟨m₀, m₁⟩ := u
      rcases cs with _ | c
      · -- The challenge encrypts under the upfront encapsulation.
        rw [G₁.outcome_challenge,
          show G₁.stateUpfront (keys, e) (some (keys, e, none), ((), ((), ()))) =
            (keys, .inl (e keys.1)) from rfl, PKE.ChallengeCCA.Game.upfront_outcome_challenge,
          fTransform_bindK, ← SymmetricEncryption.bindK_encryptions dem (e keys.1).2
            (if b then m₁ else m₀)]
        refine bindK_congr fun E _ => ?_
        rw [fTransform_single]
        rfl
      · rw [G₁.outcome_challenge_some, show G₁.stateUpfront (keys, e)
          (some (keys, e, some c), ((), ((), ()))) = (keys, .inr c) from rfl,
          PKE.ChallengeCCA.Game.upfront_outcome_challenge_inr, fTransform_single]
        rfl
    · -- Decrypting `c₁*` gives the encapsulated key, on a good sample.
      rw [G₁.outcome_dec, PKE.ChallengeCCA.Game.upfront_outcome_dec, fTransform_single]
      rcases cs with _ | c
      · by_cases h₂ : u.1 = (e keys.1).1
        · simp [G₁.stateUpfront, h₂, good]
        · simp [G₁.stateUpfront, h₂]
      · by_cases h₁ : c = u
        · subst h₁
          simp [G₁.stateUpfront]
        · by_cases h₂ : u.1 = (e keys.1).1
          · simp [G₁.stateUpfront, h₁, h₂, good]
          · simp [G₁.stateUpfront, h₁, h₂]
  · dsimp only [Distribution.ProbDist.single]
    rw [fTransform_single]
    rfl

omit [Fintype C₁] [Fintype K] [DecidableEq C₁] [DecidableEq K] [Nonempty K] in
/-- **The bad samples have mass at most the correctness error**: for `(pk, sk) ← G` and
independent encapsulations, decapsulating the encapsulation under `pk` misses its key with
probability at most `δ`. -/
lemma KEM.mass_encapsulations_le (kem : KEM PK SK C₁ K) (δ : ℝ)
    (correctnessError : kem.CorrectnessError δ) :
    (Distribution.prodProbDist kem.gen kem.encapsulations).1.mass
      (fun z => kem.decaps z.1.2 (z.2 z.1.1).1 ≠ some (z.2 z.1.1).2) ≤ δ := by
  refine le_trans (le_of_eq ?_) correctnessError
  have hlaw : fTransform (fun z : (PK × SK) × (PK → C₁ × K) => (z.1, z.2 z.1.1))
      (Distribution.prodProbDist kem.gen kem.encapsulations).1 =
      (Distribution.ProbDist.bind kem.gen fun keys =>
        Distribution.ProbDist.map (fun ck => (keys, ck)) (kem.encaps keys.1)).1 := by
    rw [Distribution.ProbDist.bind_val, Distribution.prodProbDist_val, prod_eq_bindK,
      fTransform_bindK]
    refine bindK_congr fun keys _ => ?_
    rw [fTransform_fTransform, fTransform_eq_bindK]
    refine (KEM.bindK_encapsulations kem keys.1 (fun ck => Finsupp.single (keys, ck) 1)).trans ?_
    exact (fTransform_eq_bindK _ _).symm
  rw [← hlaw, Distribution.mass_fTransform]


end Upfront

/-! ## The games as converters on the real systems

Each single-challenge game of [1, Figure 1] is the challenge converter of its notion on the real
system of the scheme: the challenge encrypts, or encapsulates, through the real system, which
samples the keys at its first query. -/

/-! ### `IND-CCA^DEM(b)` -/

section DEMChallenge

/-- The challenge of `IND-CCA^DEM(b)` on `⟦E_k, D_k⟧` as fresh sampling. -/
noncomputable def DEM.ChallengeCCA.Challenge.freshSamplingReal (dem : SymmetricEncryption K M C₂)
    (b : Bool) (q : ℕ) :
    FreshSampling (ChallengeLeftRight M C₂ q) (DEM.ChallengeCCA.Challenge M C₂ b • AE.Real dem) :=
  (((FreshSampling.source (AE.Real.law1 dem) _).parallel
    (FreshSampling.source (AE.Real.law2 dem) _)).ofProgram none _ _ _ :
      FreshSampling (AE M C₂ (DEM.ChallengeCCA.Challenge.bound M C₂ b * q)) (AE.Real dem)).ofProgram
    (A := ChallengeLeftRight M C₂ q) none (DEM.ChallengeCCA.Challenge.body M C₂ b)
    (DEM.ChallengeCCA.Challenge.bound_spec M C₂ b) fun _ hne hl => ⟨hne, hl⟩

/-- The fresh-sampling step of `⟦E_k, D_k⟧`. -/
noncomputable abbrev AE.Real.freshStep (dem : SymmetricEncryption K M C₂) :
    ProbStep (Option K × Unit × Unit) AE.Port (AE.Input M C₂) (AE.Output M C₂) :=
  (AE.Real.body dem).probCombine
    (ProbStep.parallel (ProbStep.fresh (AE.Real.law1 dem)) (ProbStep.fresh (AE.Real.law2 dem)))
    (AE.Real.bound_spec dem)

/-- The fresh-sampling step of the challenge of `IND-CCA^DEM(b)` on a step of `⟦E_k, D_k⟧`. -/
noncomputable abbrev DEM.ChallengeCCA.Challenge.freshStep (b : Bool) {R : Type}
    (stepR : ProbStep R AE.Port (AE.Input M C₂) (AE.Output M C₂)) :
    ProbStep (Option (Option C₂) × R) ChallengeLeftRight.Port (ChallengeLeftRight.Input M C₂)
      (ChallengeLeftRight.Output M C₂) :=
  (DEM.ChallengeCCA.Challenge.body M C₂ b).probCombine stepR
    (DEM.ChallengeCCA.Challenge.bound_spec M C₂ b)

omit [DecidableEq C₂] [Nonempty K] in
/-- **`⟦E_k, D_k⟧` on an encryption**: `c ← Enc_k(m)`. -/
lemma AE.Real.outcome_enc (dem : SymmetricEncryption K M C₂) (k : K) (m : M) :
    (AE.Real.freshStep dem).outcome (some k, ((), ())) ⟨.enc, m⟩ =
      bindK dem.encryptions.1 fun E => Finsupp.single ((some k, ((), ())),
        (⟨.enc, E (k, m)⟩ : Σ i, AE.Output M C₂ i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val, show AE.Real.bound dem = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩) (by simp [AE.Real.body, callProg]),
    ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun E _ => ?_
  rw [Program.probInvoke_inl (a := (some k, E (k, m)))
    (by simp [AE.Real.body, callProg, returnProg, ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

omit [DecidableEq C₂] [Nonempty K] in
/-- **`⟦E_k, D_k⟧` on a decryption**: `Dec_k(c)`. -/
lemma AE.Real.outcome_dec (dem : SymmetricEncryption K M C₂) (k : K) (c : C₂) :
    (AE.Real.freshStep dem).outcome (some k, ((), ())) ⟨.dec, c⟩ =
      Finsupp.single ((some k, ((), ())), (⟨.dec, dem.dec k c⟩ : Σ i, AE.Output M C₂ i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some k, dem.dec k c)) (by simp [AE.Real.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

omit [DecidableEq C₂] [Nonempty K] in
/-- **`⟦E_k, D_k⟧` initializes at its first query**: the key is sampled. -/
lemma AE.Real.outcome_none (dem : SymmetricEncryption K M C₂) (x : Σ i, AE.Input M C₂ i) :
    (AE.Real.freshStep dem).outcome (none, ((), ())) x =
      bindK dem.gen.1 fun k => (AE.Real.freshStep dem).outcome (some k, ((), ())) x := by
  obtain ⟨o, u⟩ := x
  conv_lhs =>
    rw [ProbStep.outcome, Program.probCombine_val, show AE.Real.bound dem = 1 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩)
        (by cases o <;> simp [AE.Real.body, callProg]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun k _ => ?_
  cases o
  · rw [AE.Real.outcome_enc, Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
        (by simp [AE.Real.body, callProg, ProbStep.inlReply]),
      ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
    refine bindK_congr fun E _ => ?_
    rw [Program.probInvoke_inl (a := (some k, E (k, u)))
      (by simp [AE.Real.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply])]
    simp [fTransform, ProbStep.tagged]
  · rw [AE.Real.outcome_dec, Program.probInvoke_inl (a := (some k, dem.dec k u))
      (by simp [AE.Real.body, callProg, returnProg, ProbStep.inlReply])]
    simp [fTransform, ProbStep.tagged]

variable {R : Type} (stepR : ProbStep R AE.Port (AE.Input M C₂) (AE.Output M C₂))

omit [DecidableEq M] in
/-- **The DEM challenge reads `⟦E_k, D_k⟧` first** before its challenge: on a system whose
replies are mixtures over states, the challenge on it is the mixture. -/
lemma DEM.ChallengeCCA.Challenge.outcome_bindK (b : Bool) (cC : Option (Option C₂))
    (hcC : cC.getD none = none) (r : R) {Z : Type} (ρ : Distribution Z) (g : Z → R)
    (h : ∀ x, stepR.outcome r x = bindK ρ fun z => stepR.outcome (g z) x)
    (x : Σ o, ChallengeLeftRight.Input M C₂ o) :
    (DEM.ChallengeCCA.Challenge.freshStep b stepR).outcome (cC, r) x =
      bindK ρ fun z => (DEM.ChallengeCCA.Challenge.freshStep b stepR).outcome (cC, g z) x := by
  have hcC' : cC = none ∨ cC = some none := by
    rcases cC with _ | _ | _ <;> simp_all
  obtain ⟨o, u⟩ := x
  have hb : DEM.ChallengeCCA.Challenge.bound M C₂ b = 0 + 1 := rfl
  cases o
  · have h0 : DEM.ChallengeCCA.Challenge.body M C₂ b cC .challenge u [] =
        .inr ⟨.enc, if b then u.2 else u.1⟩ := by
      rcases hcC' with rfl | rfl <;> simp [DEM.ChallengeCCA.Challenge.body, callProg]
    conv_lhs => rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0, h]
    conv_rhs => enter [2, z]; rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0]
    simp only [fTransform_bindK, bindK_bindK]
  · have h0 : DEM.ChallengeCCA.Challenge.body M C₂ b cC .dec u [] = .inr ⟨.dec, u⟩ := by
      rcases hcC' with rfl | rfl <;> simp [DEM.ChallengeCCA.Challenge.body, callProg]
    conv_lhs => rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0, h]
    conv_rhs => enter [2, z]; rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0]
    simp only [fTransform_bindK, bindK_bindK]

omit [DecidableEq M] in
/-- **The DEM challenge on the first challenge**: `c* ← E_k(m_b)` through `⟦E_k, D_k⟧`. -/
lemma DEM.ChallengeCCA.Challenge.outcome_challenge (b : Bool) (cC : Option (Option C₂))
    (hcC : cC.getD none = none) (r : R) (m₀ m₁ : M) (ν : Distribution (R × C₂))
    (h : stepR.outcome r ⟨.enc, if b then m₁ else m₀⟩ =
      bindK ν fun z => Finsupp.single (z.1, ⟨.enc, z.2⟩) 1) :
    (DEM.ChallengeCCA.Challenge.freshStep b stepR).outcome (cC, r) ⟨.challenge, (m₀, m₁)⟩ =
      bindK ν fun z => Finsupp.single ((some (some z.2), z.1),
        (⟨.challenge, some z.2⟩ : Σ o, ChallengeLeftRight.Output M C₂ o)) 1 := by
  have hcC' : cC = none ∨ cC = some none := by
    rcases cC with _ | _ | _ <;> simp_all
  rw [ProbStep.outcome, Program.probCombine_val,
    show DEM.ChallengeCCA.Challenge.bound M C₂ b = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.enc, if b then m₁ else m₀⟩)
      (by rcases hcC' with rfl | rfl <;> simp [DEM.ChallengeCCA.Challenge.body, callProg]), h]
  simp only [fTransform_bindK, bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_inl (a := (some (some z.2), some z.2))
    (by rcases hcC' with rfl | rfl <;>
      simp [DEM.ChallengeCCA.Challenge.body, callProg, returnProg])]
  simp [fTransform, ProbStep.tagged]

omit [DecidableEq M] in
/-- **The DEM challenge on a later challenge**: `⊥`. -/
lemma DEM.ChallengeCCA.Challenge.outcome_challenge_some (b : Bool) (cs : C₂) (r : R)
    (m₀ m₁ : M) :
    (DEM.ChallengeCCA.Challenge.freshStep b stepR).outcome (some (some cs), r)
        ⟨.challenge, (m₀, m₁)⟩ =
      Finsupp.single ((some (some cs), r),
        (⟨.challenge, none⟩ : Σ o, ChallengeLeftRight.Output M C₂ o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (some cs), none))
      (by simp [DEM.ChallengeCCA.Challenge.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

omit [DecidableEq M] in
/-- **The DEM challenge on the challenge ciphertext**: `⊥`. -/
lemma DEM.ChallengeCCA.Challenge.outcome_dec_challenge (b : Bool) (cs : C₂) (r : R) :
    (DEM.ChallengeCCA.Challenge.freshStep b stepR).outcome (some (some cs), r) ⟨.dec, cs⟩ =
      Finsupp.single ((some (some cs), r),
        (⟨.dec, none⟩ : Σ o, ChallengeLeftRight.Output M C₂ o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (some cs), none))
      (by simp [DEM.ChallengeCCA.Challenge.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

omit [DecidableEq M] in
/-- **The DEM challenge on another decryption**: `D_k(c)` through `⟦E_k, D_k⟧`. -/
lemma DEM.ChallengeCCA.Challenge.outcome_dec (b : Bool) (cC : Option (Option C₂)) (r : R)
    (c : C₂) (hc : cC.getD none ≠ some c) (ν : Distribution (R × Option M))
    (h : stepR.outcome r ⟨.dec, c⟩ = bindK ν fun z => Finsupp.single (z.1, ⟨.dec, z.2⟩) 1) :
    (DEM.ChallengeCCA.Challenge.freshStep b stepR).outcome (cC, r) ⟨.dec, c⟩ =
      bindK ν fun z => Finsupp.single ((some (cC.getD none), z.1),
        (⟨.dec, z.2⟩ : Σ o, ChallengeLeftRight.Output M C₂ o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    show DEM.ChallengeCCA.Challenge.bound M C₂ b = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.dec, c⟩)
      (by rcases cC with _ | _ | _ <;> simp_all [DEM.ChallengeCCA.Challenge.body, callProg]), h]
  simp only [fTransform_bindK, bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_inl (a := (some (cC.getD none), z.2))
    (by rcases cC with _ | _ | _ <;>
      simp_all [DEM.ChallengeCCA.Challenge.body, callProg, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **`IND-CCA^DEM(b)` initializes at its first query**: the key is sampled. -/
lemma DEM.ChallengeCCA.Game.outcome_none (dem : SymmetricEncryption K M C₂) (b : Bool)
    (x : Σ o, ChallengeLeftRight.Input M C₂ o) :
    (DEM.ChallengeCCA.Game.freshStep dem b).outcome (none, ((), ())) x =
      bindK (𝒰[K]).1 fun k =>
        (DEM.ChallengeCCA.Game.freshStep dem b).outcome (some (k, none), ((), ())) x := by
  obtain ⟨_ | _, u⟩ := x
  · obtain ⟨m₀, m₁⟩ := u
    rw [DEM.ChallengeCCA.Game.outcome_challenge_none]
    exact bindK_congr fun k _ => (DEM.ChallengeCCA.Game.outcome_challenge dem b k m₀ m₁).symm
  · rw [DEM.ChallengeCCA.Game.outcome_dec_none]
    refine bindK_congr fun k _ => ?_
    rw [DEM.ChallengeCCA.Game.outcome_dec, if_neg (by simp)]

end DEMChallenge

/-! ### `IND-CCA^PKE(b)` -/

section PKEChallengeSteps

omit [DecidableEq SK]

variable {C : Type} [Fintype C]

/-- The challenge of `IND-CCA^PKE(b)` on the public key, `E_pk` and `D_sk` as fresh sampling. -/
noncomputable def PKE.ChallengeCCA.Challenge.freshSamplingReal [DecidableEq C]
    (pke : PublicKeyEncryption PK SK M C) (b : Bool) (q : ℕ) :
    FreshSampling (PKEChallenge PK M C q) (PKE.ChallengeCCA.Challenge PK M C b • PKE.Real pke) :=
  (((FreshSampling.source (PKE.Real.law1 pke) _).parallel
    (FreshSampling.source (PKE.Real.law2 pke) _)).ofProgram none _ _ _ :
      FreshSampling (PKE PK M C (PKE.ChallengeCCA.Challenge.bound PK M C b * q))
        (PKE.Real pke)).ofProgram
    (A := PKEChallenge PK M C q) none (PKE.ChallengeCCA.Challenge.body PK M C b)
    (PKE.ChallengeCCA.Challenge.bound_spec PK M C b) fun _ hne hl => ⟨hne, hl⟩

/-- The fresh-sampling step of the public key, `E_pk` and `D_sk`. -/
noncomputable abbrev PKE.Real.freshStep (pke : PublicKeyEncryption PK SK M C) :
    ProbStep (Option (PK × SK) × Unit × Unit) PKE.Port (PKE.Input M C) (PKE.Output PK M C) :=
  (PKE.Real.body pke).probCombine
    (ProbStep.parallel (ProbStep.fresh (PKE.Real.law1 pke)) (ProbStep.fresh (PKE.Real.law2 pke)))
    (PKE.Real.bound_spec pke)

/-- The fresh-sampling step of the challenge of `IND-CCA^PKE(b)` on a step of the PKE. -/
noncomputable abbrev PKE.ChallengeCCA.Challenge.freshStep [DecidableEq C] (b : Bool) {R : Type}
    (stepR : ProbStep R PKE.Port (PKE.Input M C) (PKE.Output PK M C)) :
    ProbStep (Option (Option C) × R) PKEChallenge.Port (PKEChallenge.Input M C)
      (PKEChallenge.Output PK M C) :=
  (PKE.ChallengeCCA.Challenge.body PK M C b).probCombine stepR
    (PKE.ChallengeCCA.Challenge.bound_spec PK M C b)

/-- **The public key, `E_pk` and `D_sk` on the public key.** -/
lemma PKE.Real.outcome_publicKey (pke : PublicKeyEncryption PK SK M C) (keys : PK × SK) :
    (PKE.Real.freshStep pke).outcome (some keys, ((), ())) ⟨.publicKey, ()⟩ =
      Finsupp.single ((some keys, ((), ())),
        (⟨.publicKey, keys.1⟩ : Σ i, PKE.Output PK M C i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some keys, keys.1)) (by simp [PKE.Real.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **The public key, `E_pk` and `D_sk` on an encryption**: `c ← E(pk, m)`. -/
lemma PKE.Real.outcome_enc (pke : PublicKeyEncryption PK SK M C) (keys : PK × SK) (m : M) :
    (PKE.Real.freshStep pke).outcome (some keys, ((), ())) ⟨.enc, m⟩ =
      bindK pke.encryptions.1 fun E => Finsupp.single ((some keys, ((), ())),
        (⟨.enc, E (keys.1, m)⟩ : Σ i, PKE.Output PK M C i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val, show PKE.Real.bound pke = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩) (by simp [PKE.Real.body, callProg]),
    ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun E _ => ?_
  rw [Program.probInvoke_inl (a := (some keys, E (keys.1, m)))
    (by simp [PKE.Real.body, callProg, returnProg, ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

/-- **The public key, `E_pk` and `D_sk` on a decryption**: `D(sk, c)`. -/
lemma PKE.Real.outcome_dec (pke : PublicKeyEncryption PK SK M C) (keys : PK × SK) (c : C) :
    (PKE.Real.freshStep pke).outcome (some keys, ((), ())) ⟨.dec, c⟩ =
      Finsupp.single ((some keys, ((), ())),
        (⟨.dec, pke.dec keys.2 c⟩ : Σ i, PKE.Output PK M C i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some keys, pke.dec keys.2 c))
      (by simp [PKE.Real.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **The public key, `E_pk` and `D_sk` initialize at the first query**: the keys are sampled. -/
lemma PKE.Real.outcome_none (pke : PublicKeyEncryption PK SK M C) (x : Σ i, PKE.Input M C i) :
    (PKE.Real.freshStep pke).outcome (none, ((), ())) x =
      bindK pke.gen.1 fun keys => (PKE.Real.freshStep pke).outcome (some keys, ((), ())) x := by
  obtain ⟨o, u⟩ := x
  conv_lhs =>
    rw [ProbStep.outcome, Program.probCombine_val, show PKE.Real.bound pke = 1 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩)
        (by cases o <;> simp [PKE.Real.body, callProg]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun keys _ => ?_
  cases o
  · obtain ⟨⟩ := u
    rw [PKE.Real.outcome_publicKey, Program.probInvoke_inl (a := (some keys, keys.1))
      (by simp [PKE.Real.body, callProg, returnProg, ProbStep.inlReply])]
    simp [fTransform, ProbStep.tagged]
  · rw [PKE.Real.outcome_enc, Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
        (by simp [PKE.Real.body, callProg, ProbStep.inlReply]),
      ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
    refine bindK_congr fun E _ => ?_
    rw [Program.probInvoke_inl (a := (some keys, E (keys.1, u)))
      (by simp [PKE.Real.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply])]
    simp [fTransform, ProbStep.tagged]
  · rw [PKE.Real.outcome_dec, Program.probInvoke_inl (a := (some keys, pke.dec keys.2 u))
      (by simp [PKE.Real.body, callProg, returnProg, ProbStep.inlReply])]
    simp [fTransform, ProbStep.tagged]

variable [DecidableEq C] {R : Type}
  (stepR : ProbStep R PKE.Port (PKE.Input M C) (PKE.Output PK M C))

omit [DecidableEq PK] [DecidableEq M] in
/-- **The PKE challenge reads the PKE first** before its challenge: on a PKE whose replies are
mixtures over states, the challenge on it is the mixture. -/
lemma PKE.ChallengeCCA.Challenge.outcome_bindK (b : Bool) (cC : Option (Option C))
    (hcC : cC.getD none = none) (r : R) {Z : Type} (ρ : Distribution Z) (g : Z → R)
    (h : ∀ x, stepR.outcome r x = bindK ρ fun z => stepR.outcome (g z) x)
    (x : Σ o, PKEChallenge.Input M C o) :
    (PKE.ChallengeCCA.Challenge.freshStep b stepR).outcome (cC, r) x =
      bindK ρ fun z => (PKE.ChallengeCCA.Challenge.freshStep b stepR).outcome (cC, g z) x := by
  have hcC' : cC = none ∨ cC = some none := by
    rcases cC with _ | _ | _ <;> simp_all
  obtain ⟨o, u⟩ := x
  have hb : PKE.ChallengeCCA.Challenge.bound PK M C b = 0 + 1 := rfl
  cases o
  · have h0 : PKE.ChallengeCCA.Challenge.body PK M C b cC .publicKey u [] =
        .inr ⟨.publicKey, ()⟩ := by
      rcases hcC' with rfl | rfl <;> simp [PKE.ChallengeCCA.Challenge.body, callProg]
    conv_lhs => rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0, h]
    conv_rhs => enter [2, z]; rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0]
    simp only [fTransform_bindK, bindK_bindK]
  · have h0 : PKE.ChallengeCCA.Challenge.body PK M C b cC .challenge u [] =
        .inr ⟨.enc, if b then u.2 else u.1⟩ := by
      rcases hcC' with rfl | rfl <;> simp [PKE.ChallengeCCA.Challenge.body, callProg]
    conv_lhs => rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0, h]
    conv_rhs => enter [2, z]; rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0]
    simp only [fTransform_bindK, bindK_bindK]
  · have h0 : PKE.ChallengeCCA.Challenge.body PK M C b cC .dec u [] = .inr ⟨.dec, u⟩ := by
      rcases hcC' with rfl | rfl <;> simp [PKE.ChallengeCCA.Challenge.body, callProg]
    conv_lhs => rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0, h]
    conv_rhs => enter [2, z]; rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0]
    simp only [fTransform_bindK, bindK_bindK]

omit [DecidableEq PK] [DecidableEq M] in
/-- **The PKE challenge on the public key**: the public key of the PKE. -/
lemma PKE.ChallengeCCA.Challenge.outcome_publicKey (b : Bool) (cC : Option (Option C)) (r : R)
    (ν : Distribution (R × PK))
    (h : stepR.outcome r ⟨.publicKey, ()⟩ =
      bindK ν fun z => Finsupp.single (z.1, ⟨.publicKey, z.2⟩) 1) :
    (PKE.ChallengeCCA.Challenge.freshStep b stepR).outcome (cC, r) ⟨.publicKey, ()⟩ =
      bindK ν fun z => Finsupp.single ((some (cC.getD none), z.1),
        (⟨.publicKey, z.2⟩ : Σ o, PKEChallenge.Output PK M C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    show PKE.ChallengeCCA.Challenge.bound PK M C b = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.publicKey, ()⟩)
      (by cases cC <;> simp [PKE.ChallengeCCA.Challenge.body, callProg]), h]
  simp only [fTransform_bindK, bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_inl (a := (some (cC.getD none), z.2))
    (by cases cC <;> simp [PKE.ChallengeCCA.Challenge.body, callProg, returnProg])]
  simp [fTransform, ProbStep.tagged]

omit [DecidableEq PK] [DecidableEq M] in
/-- **The PKE challenge on the first challenge**: `c* ← E(pk, m_b)` through the PKE. -/
lemma PKE.ChallengeCCA.Challenge.outcome_challenge (b : Bool) (cC : Option (Option C))
    (hcC : cC.getD none = none) (r : R) (m₀ m₁ : M) (ν : Distribution (R × C))
    (h : stepR.outcome r ⟨.enc, if b then m₁ else m₀⟩ =
      bindK ν fun z => Finsupp.single (z.1, ⟨.enc, z.2⟩) 1) :
    (PKE.ChallengeCCA.Challenge.freshStep b stepR).outcome (cC, r) ⟨.challenge, (m₀, m₁)⟩ =
      bindK ν fun z => Finsupp.single ((some (some z.2), z.1),
        (⟨.challenge, some z.2⟩ : Σ o, PKEChallenge.Output PK M C o)) 1 := by
  have hcC' : cC = none ∨ cC = some none := by
    rcases cC with _ | _ | _ <;> simp_all
  rw [ProbStep.outcome, Program.probCombine_val,
    show PKE.ChallengeCCA.Challenge.bound PK M C b = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.enc, if b then m₁ else m₀⟩)
      (by rcases hcC' with rfl | rfl <;> simp [PKE.ChallengeCCA.Challenge.body, callProg]), h]
  simp only [fTransform_bindK, bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_inl (a := (some (some z.2), some z.2))
    (by rcases hcC' with rfl | rfl <;>
      simp [PKE.ChallengeCCA.Challenge.body, callProg, returnProg])]
  simp [fTransform, ProbStep.tagged]

omit [DecidableEq PK] [DecidableEq M] in
/-- **The PKE challenge on a later challenge**: `⊥`. -/
lemma PKE.ChallengeCCA.Challenge.outcome_challenge_some (b : Bool) (cs : C) (r : R)
    (m₀ m₁ : M) :
    (PKE.ChallengeCCA.Challenge.freshStep b stepR).outcome (some (some cs), r)
        ⟨.challenge, (m₀, m₁)⟩ =
      Finsupp.single ((some (some cs), r),
        (⟨.challenge, none⟩ : Σ o, PKEChallenge.Output PK M C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (some cs), none))
      (by simp [PKE.ChallengeCCA.Challenge.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

omit [DecidableEq PK] [DecidableEq M] in
/-- **The PKE challenge on the challenge ciphertext**: `⊥`. -/
lemma PKE.ChallengeCCA.Challenge.outcome_dec_challenge (b : Bool) (cs : C) (r : R) :
    (PKE.ChallengeCCA.Challenge.freshStep b stepR).outcome (some (some cs), r) ⟨.dec, cs⟩ =
      Finsupp.single ((some (some cs), r),
        (⟨.dec, none⟩ : Σ o, PKEChallenge.Output PK M C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (some cs), none))
      (by simp [PKE.ChallengeCCA.Challenge.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

omit [DecidableEq PK] [DecidableEq M] in
/-- **The PKE challenge on another decryption**: `D(sk, c)` through the PKE. -/
lemma PKE.ChallengeCCA.Challenge.outcome_dec (b : Bool) (cC : Option (Option C)) (r : R)
    (c : C) (hc : cC.getD none ≠ some c) (ν : Distribution (R × Option M))
    (h : stepR.outcome r ⟨.dec, c⟩ = bindK ν fun z => Finsupp.single (z.1, ⟨.dec, z.2⟩) 1) :
    (PKE.ChallengeCCA.Challenge.freshStep b stepR).outcome (cC, r) ⟨.dec, c⟩ =
      bindK ν fun z => Finsupp.single ((some (cC.getD none), z.1),
        (⟨.dec, z.2⟩ : Σ o, PKEChallenge.Output PK M C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    show PKE.ChallengeCCA.Challenge.bound PK M C b = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.dec, c⟩)
      (by rcases cC with _ | _ | _ <;> simp_all [PKE.ChallengeCCA.Challenge.body, callProg]), h]
  simp only [fTransform_bindK, bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_inl (a := (some (cC.getD none), z.2))
    (by rcases cC with _ | _ | _ <;>
      simp_all [PKE.ChallengeCCA.Challenge.body, callProg, returnProg])]
  simp [fTransform, ProbStep.tagged]

end PKEChallengeSteps

/-! ### `IND-CCA^KEM(b)` -/

/-- The fresh-sampling step of `KEM-real`. -/
noncomputable abbrev KEM.Real.freshStep (kem : KEM PK SK C₁ K) :
    ProbStep (Option (PK × SK) × Unit × Unit) Encapsulation.Port (Encapsulation.Input C₁)
      (Encapsulation.Output PK C₁ K) :=
  (KEM.Real.body kem).probCombine
    (ProbStep.parallel (ProbStep.fresh (KEM.Real.law1 kem)) (ProbStep.fresh (KEM.Real.law2 kem)))
    (KEM.Real.bound_spec kem)

section KEMReal

omit [DecidableEq SK] [DecidableEq C₁] [DecidableEq K] [Nonempty K]

/-- **`KEM-real` on the public key.** -/
lemma KEM.Real.outcome_publicKey (kem : KEM PK SK C₁ K) (keys : PK × SK) :
    (KEM.Real.freshStep kem).outcome (some keys, ((), ())) ⟨.publicKey, ()⟩ =
      Finsupp.single ((some keys, ((), ())),
        (⟨.publicKey, keys.1⟩ : Σ i, Encapsulation.Output PK C₁ K i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some keys, keys.1)) (by simp [KEM.Real.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **`KEM-real` on an encapsulation**: `(c, k) ← Enc(pk)`. -/
lemma KEM.Real.outcome_encaps (kem : KEM PK SK C₁ K) (keys : PK × SK) :
    (KEM.Real.freshStep kem).outcome (some keys, ((), ())) ⟨.encaps, ()⟩ =
      bindK kem.encapsulations.1 fun e => Finsupp.single ((some keys, ((), ())),
        (⟨.encaps, e keys.1⟩ : Σ i, Encapsulation.Output PK C₁ K i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val, show KEM.Real.bound kem = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩) (by simp [KEM.Real.body, callProg]),
    ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun e _ => ?_
  rw [Program.probInvoke_inl (a := (some keys, e keys.1))
    (by simp [KEM.Real.body, callProg, returnProg, ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`KEM-real` initializes at its first query**: the keys are sampled. -/
lemma KEM.Real.outcome_none (kem : KEM PK SK C₁ K) (x : Σ i, Encapsulation.Input C₁ i) :
    (KEM.Real.freshStep kem).outcome (none, ((), ())) x =
      bindK kem.gen.1 fun keys => (KEM.Real.freshStep kem).outcome (some keys, ((), ())) x := by
  obtain ⟨o, u⟩ := x
  conv_lhs =>
    rw [ProbStep.outcome, Program.probCombine_val, show KEM.Real.bound kem = 1 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩)
        (by cases o <;> simp [KEM.Real.body, callProg]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun keys _ => ?_
  cases o
  · obtain ⟨⟩ := u
    rw [KEM.Real.outcome_publicKey, Program.probInvoke_inl (a := (some keys, keys.1))
      (by simp [KEM.Real.body, callProg, returnProg, ProbStep.inlReply])]
    simp [fTransform, ProbStep.tagged]
  · obtain ⟨⟩ := u
    rw [KEM.Real.outcome_encaps, Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
        (by simp [KEM.Real.body, callProg, ProbStep.inlReply]),
      ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
    refine bindK_congr fun e _ => ?_
    rw [Program.probInvoke_inl (a := (some keys, e keys.1))
      (by simp [KEM.Real.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply])]
    simp [fTransform, ProbStep.tagged]
  · rw [Program.probInvoke_inl (a := (some keys, kem.decaps keys.2 u))
      (by simp [KEM.Real.body, callProg, returnProg, ProbStep.inlReply])]
    rw [ProbStep.outcome, Program.probCombine_val, Program.probInvoke_inl
      (a := (some keys, kem.decaps keys.2 u)) (by simp [KEM.Real.body, returnProg])]

end KEMReal

section KEMChallengeSteps

omit [DecidableEq SK] [DecidableEq K]

omit [DecidableEq C₁] [Nonempty K] in
/-- **`KEM-real` on a decapsulation**: `D(sk, c)`. -/
lemma KEM.Real.outcome_decaps (kem : KEM PK SK C₁ K) (keys : PK × SK) (c : C₁) :
    (KEM.Real.freshStep kem).outcome (some keys, ((), ())) ⟨.decaps, c⟩ =
      Finsupp.single ((some keys, ((), ())),
        (⟨.decaps, kem.decaps keys.2 c⟩ : Σ i, Encapsulation.Output PK C₁ K i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some keys, kem.decaps keys.2 c))
      (by simp [KEM.Real.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- The challenge of `IND-CCA^KEM(b)` on `KEM-real` as fresh sampling. -/
noncomputable def KEM.ChallengeCCA.Challenge.freshSamplingReal (kem : KEM PK SK C₁ K) (b : Bool)
    (q : ℕ) :
    FreshSampling (KEMChallenge PK C₁ K q) (KEM.ChallengeCCA.Challenge PK C₁ K b • KEM.Real kem) :=
  FreshSampling.ofRightContext _
    (((((FreshSampling.source (KEM.Real.law1 kem) _).parallel
      (FreshSampling.source (KEM.Real.law2 kem) _)).ofProgram none _ _ _ :
        FreshSampling (Encapsulation PK C₁ K (KEM.ChallengeCCA.Challenge.bound PK C₁ K b * q))
          (KEM.Real kem)).parallel
      ((FreshSampling.source (KEM.ChallengeCCA.Challenge.law1 PK C₁ K b) _).parallel
        (FreshSampling.source (KEM.ChallengeCCA.Challenge.law2 PK C₁ K b) _))).ofProgram
      none _ _ _)

/-- The fresh-sampling step of the challenge of `IND-CCA^KEM(b)` on a step of the KEM. -/
noncomputable abbrev KEM.ChallengeCCA.Challenge.freshStep (b : Bool) {R : Type}
    (stepR :
      ProbStep R Encapsulation.Port (Encapsulation.Input C₁) (Encapsulation.Output PK C₁ K)) :
    ProbStep (Option (Option (PK × C₁ × K)) × R × Unit × Unit) KEMChallenge.Port
      (KEMChallenge.Input C₁) (KEMChallenge.Output PK C₁ K) :=
  (KEM.ChallengeCCA.Challenge.body PK C₁ K b).probCombine
    (ProbStep.parallel stepR
      (ProbStep.parallel (ProbStep.fresh (KEM.ChallengeCCA.Challenge.law1 PK C₁ K b))
        (ProbStep.fresh (KEM.ChallengeCCA.Challenge.law2 PK C₁ K b))))
    (KEM.ChallengeCCA.Challenge.bound_spec PK C₁ K b)

/-- **`IND-CCA^KEM(b)` initializes at its first query**: the keys, `k₁` and the encapsulations
are sampled. -/
lemma KEM.ChallengeCCA.Game.outcome_none (kem : KEM PK SK C₁ K) (b : Bool)
    (x : Σ i, KEMChallenge.Input C₁ i) :
    (KEM.ChallengeCCA.Game.freshStep kem b).outcome (none, ((), ((), ()))) x =
      bindK kem.gen.1 fun keys => bindK (𝒰[K]).1 fun k₁ => bindK kem.encapsulations.1 fun e =>
        (KEM.ChallengeCCA.Game.freshStep kem b).outcome (some (keys, k₁, e), ((), ((), ()))) x := by
  obtain ⟨_ | _, u⟩ := x
  · obtain ⟨⟩ := u
    rw [KEM.ChallengeCCA.Game.outcome_input_none]
    exact bindK_congr fun keys _ => bindK_congr fun k₁ _ => bindK_congr fun e _ =>
      (KEM.ChallengeCCA.Game.outcome_input kem b keys k₁ e).symm
  · conv_lhs =>
      rw [ProbStep.outcome, Program.probCombine_val,
        show KEM.ChallengeCCA.Game.bound kem b = 2 + 1 from rfl,
        Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩)
          (by simp [KEM.ChallengeCCA.Game.body, callProg]),
        ProbStep.outcome_parallel_inl]
      simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
        Function.comp_def, fTransform_bindK, ProbStep.tagged]
    refine bindK_congr fun keys _ => ?_
    conv_lhs =>
      rw [Program.probInvoke_succ_inr (q := ⟨.inr (.inl ()), ()⟩)
          (by simp [KEM.ChallengeCCA.Game.body, callProg, ProbStep.inlReply]),
        ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inl]
      simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
        Function.comp_def, fTransform_bindK, ProbStep.tagged]
    refine bindK_congr fun k₁ _ => ?_
    conv_lhs =>
      rw [Program.probInvoke_succ_inr (q := ⟨.inr (.inr ()), ()⟩)
          (by simp [KEM.ChallengeCCA.Game.body, callProg, ProbStep.inlReply, ProbStep.inrReply]),
        ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr]
      simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
        Function.comp_def, fTransform_bindK, ProbStep.tagged]
    refine bindK_congr fun e _ => ?_
    rw [KEM.ChallengeCCA.Game.outcome_dec, Program.probInvoke_inl
      (a := (some (keys, k₁, e), if u = (e keys.1).1 then none else kem.decaps keys.2 u))
      (by by_cases h : u = (e keys.1).1 <;>
        simp [KEM.ChallengeCCA.Game.body, callProg, returnProg, ProbStep.inlReply,
          ProbStep.inrReply, h])]
    simp [fTransform, ProbStep.tagged]

variable {R : Type}
  (stepR : ProbStep R Encapsulation.Port (Encapsulation.Input C₁) (Encapsulation.Output PK C₁ K))

omit [DecidableEq PK] in
/-- **The KEM challenge reads the public key first** before its challenge: on a KEM whose public
key is a mixture over states, the challenge on it is the mixture. -/
lemma KEM.ChallengeCCA.Challenge.outcome_bindK (b : Bool) (cC : Option (Option (PK × C₁ × K)))
    (hcC : cC.getD none = none) (r : R) {Z : Type} (ρ : Distribution Z) (g : Z → R)
    (h : stepR.outcome r ⟨.publicKey, ()⟩ =
      bindK ρ fun z => stepR.outcome (g z) ⟨.publicKey, ()⟩)
    (x : Σ i, KEMChallenge.Input C₁ i) :
    (KEM.ChallengeCCA.Challenge.freshStep b stepR).outcome (cC, (r, ((), ()))) x =
      bindK ρ fun z =>
        (KEM.ChallengeCCA.Challenge.freshStep b stepR).outcome (cC, (g z, ((), ()))) x := by
  have hcC' : cC = none ∨ cC = some none := by
    rcases cC with _ | _ | _ <;> simp_all
  obtain ⟨o, u⟩ := x
  have h0 : KEM.ChallengeCCA.Challenge.body PK C₁ K b cC o u [] = .inr ⟨.inl .publicKey, ()⟩ := by
    rcases hcC' with rfl | rfl <;> cases o <;> simp [KEM.ChallengeCCA.Challenge.body, callProg]
  have hb : KEM.ChallengeCCA.Challenge.bound PK C₁ K b = 3 + 1 := rfl
  conv_lhs => rw [ProbStep.outcome, Program.probCombine_val, hb,
    Program.probInvoke_succ_inr h0, ProbStep.outcome_parallel_inl, h]
  conv_rhs => enter [2, z]; rw [ProbStep.outcome, Program.probCombine_val, hb,
    Program.probInvoke_succ_inr h0, ProbStep.outcome_parallel_inl]
  simp only [fTransform_bindK, bindK_bindK, bindK_fTransform, Function.comp_def]

omit [DecidableEq PK] in
/-- **The KEM challenge on the input, once encapsulated**: the recorded `(pk, c*, k_b)`. -/
lemma KEM.ChallengeCCA.Challenge.outcome_input_some (b : Bool) (v : PK × C₁ × K) (r : R) :
    (KEM.ChallengeCCA.Challenge.freshStep b stepR).outcome (some (some v), (r, ((), ())))
        ⟨.input, ()⟩ =
      Finsupp.single ((some (some v), (r, ((), ()))),
        (⟨.input, v⟩ : Σ i, KEMChallenge.Output PK C₁ K i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (some v), v))
      (by simp [KEM.ChallengeCCA.Challenge.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

omit [DecidableEq PK] in
/-- **The KEM challenge on a decapsulation, once encapsulated**: `⊥` on `c*`, otherwise the
decapsulation of the KEM. -/
lemma KEM.ChallengeCCA.Challenge.outcome_dec_some (b : Bool) (v : PK × C₁ × K) (r : R)
    (c : C₁) (kd : Option K)
    (hdec : c ≠ v.2.1 → stepR.outcome r ⟨.decaps, c⟩ = Finsupp.single (r, ⟨.decaps, kd⟩) 1) :
    (KEM.ChallengeCCA.Challenge.freshStep b stepR).outcome (some (some v), (r, ((), ())))
        ⟨.dec, c⟩ =
      Finsupp.single ((some (some v), (r, ((), ()))),
        (⟨.dec, if c = v.2.1 then none else kd⟩ : Σ i, KEMChallenge.Output PK C₁ K i)) 1 := by
  by_cases hc : c = v.2.1
  · rw [ProbStep.outcome, Program.probCombine_val,
      Program.probInvoke_inl (a := (some (some v), none))
        (by simp [KEM.ChallengeCCA.Challenge.body, returnProg, hc])]
    simp [fTransform, ProbStep.tagged, hc]
  · rw [ProbStep.outcome, Program.probCombine_val,
      show KEM.ChallengeCCA.Challenge.bound PK C₁ K b = 3 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl .decaps, c⟩)
        (by simp [KEM.ChallengeCCA.Challenge.body, callProg, hc]),
      ProbStep.outcome_parallel_inl, hdec hc]
    simp only [fTransform_single, bindK_single, one_smul]
    rw [Program.probInvoke_inl (a := (some (some v), kd))
      (by simp [KEM.ChallengeCCA.Challenge.body, callProg, returnProg, ProbStep.inlReply, hc])]
    simp [fTransform, ProbStep.tagged, hc]

omit [DecidableEq PK] in
/-- **The KEM challenge on the first input**: `(pk, c*, k_b)` for the public key `pk` and an
encapsulation `(c*, k₀)` of the KEM and `k₁ ← K`. -/
lemma KEM.ChallengeCCA.Challenge.outcome_input (b : Bool) (cC : Option (Option (PK × C₁ × K)))
    (hcC : cC.getD none = none) (r : R) (pk : PK)
    (hpk : stepR.outcome r ⟨.publicKey, ()⟩ = Finsupp.single (r, ⟨.publicKey, pk⟩) 1)
    {Z : Type} (μ : Distribution Z) (f : Z → C₁ × K)
    (henc : stepR.outcome r ⟨.encaps, ()⟩ =
      bindK μ fun z => Finsupp.single (r, ⟨.encaps, f z⟩) 1) :
    (KEM.ChallengeCCA.Challenge.freshStep b stepR).outcome (cC, (r, ((), ()))) ⟨.input, ()⟩ =
      bindK μ fun z => bindK (𝒰[K]).1 fun k₁ =>
        Finsupp.single ((some (some (pk, (f z).1, if b then k₁ else (f z).2)), (r, ((), ()))),
          (⟨.input, (pk, (f z).1, if b then k₁ else (f z).2)⟩ :
            Σ i, KEMChallenge.Output PK C₁ K i)) 1 := by
  have hcC' : cC = none ∨ cC = some none := by
    rcases cC with _ | _ | _ <;> simp_all
  rw [ProbStep.outcome, Program.probCombine_val,
    show KEM.ChallengeCCA.Challenge.bound PK C₁ K b = 3 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl .publicKey, ()⟩)
      (by rcases hcC' with rfl | rfl <;> simp [KEM.ChallengeCCA.Challenge.body, callProg]),
    ProbStep.outcome_parallel_inl, hpk]
  simp only [fTransform_single, bindK_single, one_smul]
  rw [Program.probInvoke_succ_inr (q := ⟨.inl .encaps, ()⟩)
      (by rcases hcC' with rfl | rfl <;>
        simp [KEM.ChallengeCCA.Challenge.body, callProg, ProbStep.inlReply]),
    ProbStep.outcome_parallel_inl, henc]
  simp only [fTransform_bindK, fTransform_single, bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_succ_inr (q := ⟨.inr (.inl ()), ()⟩)
      (by rcases hcC' with rfl | rfl <;>
        simp [KEM.ChallengeCCA.Challenge.body, callProg, ProbStep.inlReply]),
    ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inl]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun k₁ _ => ?_
  rw [Program.probInvoke_inl
    (a := (some (some (pk, (f z).1, if b then k₁ else (f z).2)),
      (pk, (f z).1, if b then k₁ else (f z).2)))
    (by rcases hcC' with rfl | rfl <;>
      simp [KEM.ChallengeCCA.Challenge.body, callProg, returnProg, ProbStep.inlReply,
        ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

omit [DecidableEq PK] in
/-- **The KEM challenge on a first decapsulation**: it encapsulates as on the first input, then
`⊥` on `c*`, otherwise the decapsulation of the KEM. -/
lemma KEM.ChallengeCCA.Challenge.outcome_dec (b : Bool) (cC : Option (Option (PK × C₁ × K)))
    (hcC : cC.getD none = none) (r : R) (pk : PK)
    (hpk : stepR.outcome r ⟨.publicKey, ()⟩ = Finsupp.single (r, ⟨.publicKey, pk⟩) 1)
    {Z : Type} (μ : Distribution Z) (f : Z → C₁ × K)
    (henc : stepR.outcome r ⟨.encaps, ()⟩ =
      bindK μ fun z => Finsupp.single (r, ⟨.encaps, f z⟩) 1)
    (c : C₁) (kd : Option K)
    (hdec : stepR.outcome r ⟨.decaps, c⟩ = Finsupp.single (r, ⟨.decaps, kd⟩) 1) :
    (KEM.ChallengeCCA.Challenge.freshStep b stepR).outcome (cC, (r, ((), ()))) ⟨.dec, c⟩ =
      bindK μ fun z => bindK (𝒰[K]).1 fun k₁ =>
        Finsupp.single ((some (some (pk, (f z).1, if b then k₁ else (f z).2)), (r, ((), ()))),
          (⟨.dec, if c = (f z).1 then none else kd⟩ : Σ i, KEMChallenge.Output PK C₁ K i)) 1 := by
  have hcC' : cC = none ∨ cC = some none := by
    rcases cC with _ | _ | _ <;> simp_all
  rw [ProbStep.outcome, Program.probCombine_val,
    show KEM.ChallengeCCA.Challenge.bound PK C₁ K b = 3 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl .publicKey, ()⟩)
      (by rcases hcC' with rfl | rfl <;> simp [KEM.ChallengeCCA.Challenge.body, callProg]),
    ProbStep.outcome_parallel_inl, hpk]
  simp only [fTransform_single, bindK_single, one_smul]
  rw [Program.probInvoke_succ_inr (q := ⟨.inl .encaps, ()⟩)
      (by rcases hcC' with rfl | rfl <;>
        simp [KEM.ChallengeCCA.Challenge.body, callProg, ProbStep.inlReply]),
    ProbStep.outcome_parallel_inl, henc]
  simp only [fTransform_bindK, fTransform_single, bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_succ_inr (q := ⟨.inr (.inr ()), ()⟩)
      (by rcases hcC' with rfl | rfl <;>
        simp [KEM.ChallengeCCA.Challenge.body, callProg, ProbStep.inlReply]),
    ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun k₁ _ => ?_
  by_cases hc : c = (f z).1
  · rw [Program.probInvoke_inl
      (a := (some (some (pk, (f z).1, if b then k₁ else (f z).2)), none))
      (by rcases hcC' with rfl | rfl <;>
        simp [KEM.ChallengeCCA.Challenge.body, callProg, returnProg, ProbStep.inlReply,
          ProbStep.inrReply, hc])]
    simp [fTransform, ProbStep.tagged, hc]
  · rw [Program.probInvoke_succ_inr (q := ⟨.inl .decaps, c⟩)
        (by rcases hcC' with rfl | rfl <;>
          simp [KEM.ChallengeCCA.Challenge.body, callProg, ProbStep.inlReply,
            ProbStep.inrReply, hc]),
      ProbStep.outcome_parallel_inl, hdec]
    simp only [fTransform_single, bindK_single, one_smul]
    rw [Program.probInvoke_inl
      (a := (some (some (pk, (f z).1, if b then k₁ else (f z).2)), kd))
      (by rcases hcC' with rfl | rfl <;>
        simp [KEM.ChallengeCCA.Challenge.body, callProg, returnProg, ProbStep.inlReply,
          ProbStep.inrReply, hc])]
    simp [fTransform, ProbStep.tagged, hc]

end KEMChallengeSteps

section Presentations

/-- **`IND-CCA^DEM(b)` is the challenge on `⟦E_k, D_k⟧`** for a uniform key `k ←$ K`. -/
lemma DEM.ChallengeCCA.Game.eq_real (dem : SymmetricEncryption K M C₂) (b : Bool) {q : ℕ} :
    DEM.ChallengeCCA.Game dem b (budget := q) =
      DEM.ChallengeCCA.Challenge M C₂ b • AE.Real { dem with gen := 𝒰[K] } := by
  -- Once `⟦E_k, D_k⟧` has its key, the challenge on it steps as `IND-CCA^DEM(b)`.
  have hsome : ∀ (cC : Option (Option C₂)) (k : K) (x : Σ o, ChallengeLeftRight.Input M C₂ o),
      (DEM.ChallengeCCA.Challenge.freshStep b
          (AE.Real.freshStep { dem with gen := 𝒰[K] })).outcome (cC, (some k, ((), ()))) x =
        fTransform (Prod.map (fun s => (s.1.map Prod.snd, (s.1.map Prod.fst, ((), ())))) id)
          ((DEM.ChallengeCCA.Game.freshStep dem b).outcome
            (some (k, cC.getD none), ((), ())) x) := by
    rintro cC k ⟨_ | _, u⟩
    · obtain ⟨m₀, m₁⟩ := u
      have henc : (AE.Real.freshStep { dem with gen := 𝒰[K] }).outcome (some k, ((), ()))
          ⟨.enc, if b then m₁ else m₀⟩ = bindK (bindK dem.encryptions.1 fun E =>
            Finsupp.single ((some k, ((), ())), E (k, if b then m₁ else m₀)) 1)
              fun z => Finsupp.single (z.1, ⟨.enc, z.2⟩) 1 := by
        rw [AE.Real.outcome_enc, bindK_bindK]
        exact bindK_congr fun E _ => by rw [bindK_single, one_smul]
      rcases cC with _ | _ | cs
      · rw [DEM.ChallengeCCA.Challenge.outcome_challenge _ b none rfl _ m₀ m₁ _ henc,
          Option.getD_none, DEM.ChallengeCCA.Game.outcome_challenge, fTransform_bindK,
          bindK_bindK]
        refine bindK_congr fun E _ => ?_
        rw [bindK_single, one_smul, fTransform_single]
        rfl
      · rw [DEM.ChallengeCCA.Challenge.outcome_challenge _ b (some none) rfl _ m₀ m₁ _ henc,
          Option.getD_some, DEM.ChallengeCCA.Game.outcome_challenge, fTransform_bindK,
          bindK_bindK]
        refine bindK_congr fun E _ => ?_
        rw [bindK_single, one_smul, fTransform_single]
        rfl
      · rw [DEM.ChallengeCCA.Challenge.outcome_challenge_some, Option.getD_some,
          DEM.ChallengeCCA.Game.outcome_challenge_some, fTransform_single]
        rfl
    · by_cases hc : cC.getD none = some u
      · obtain rfl : cC = some (some u) := by rcases cC with _ | _ | _ <;> simp_all
        rw [DEM.ChallengeCCA.Challenge.outcome_dec_challenge, Option.getD_some,
          DEM.ChallengeCCA.Game.outcome_dec, if_pos rfl, fTransform_single]
        rfl
      · rw [DEM.ChallengeCCA.Challenge.outcome_dec _ b cC _ u hc
          (Finsupp.single ((some k, ((), ())), dem.dec k u) 1)
          (by rw [AE.Real.outcome_dec, bindK_single, one_smul]),
          DEM.ChallengeCCA.Game.outcome_dec, if_neg hc, bindK_single, one_smul,
          fTransform_single]
        rfl
  refine (DEM.ChallengeCCA.Game.freshSampling dem b q).eq_fresh.trans
    (Eq.trans ?_
      (DEM.ChallengeCCA.Challenge.freshSamplingReal { dem with gen := 𝒰[K] } b q).eq_fresh.symm)
  refine Resource.ofProbAutomaton_eq_of_map _ _ _ _
    (fun s => (s.1.map Prod.snd, (s.1.map Prod.fst, ((), ())))) ?_ ?_ <;>
    dsimp only [DEM.ChallengeCCA.Game.freshSampling, DEM.ChallengeCCA.Challenge.freshSamplingReal,
      FreshSampling.ofProgram, FreshSampling.parallel, FreshSampling.source,
      Distribution.ProbDist.single]
  · rintro ⟨_ | ⟨k, cs⟩, ⟨⟩, ⟨⟩⟩ x
    · -- Both sample the key at the first query.
      refine (DEM.ChallengeCCA.Challenge.outcome_bindK
        (AE.Real.freshStep { dem with gen := 𝒰[K] }) b none rfl (none, ((), ())) (𝒰[K]).1
          (fun k => (some k, ((), ()))) (AE.Real.outcome_none { dem with gen := 𝒰[K] }) x).trans ?_
      rw [DEM.ChallengeCCA.Game.outcome_none, fTransform_bindK]
      exact bindK_congr fun k _ => hsome none k x
    · exact hsome (some cs) k x
  · rw [fTransform_single]
    rfl

omit [DecidableEq SK] in
/-- **`IND-CCA^PKE(b)` is the challenge on the public key, `E_pk` and `D_sk`.** -/
lemma PKE.ChallengeCCA.Game.eq_real {C : Type} [Fintype C] [DecidableEq C]
    (pke : PublicKeyEncryption PK SK M C) (b : Bool) {q : ℕ} :
    PKE.ChallengeCCA.Game pke b (budget := q) =
      PKE.ChallengeCCA.Challenge PK M C b • PKE.Real pke := by
  -- Once the PKE has its keys, the challenge on it steps as `IND-CCA^PKE(b)`.
  have hsome : ∀ (cC : Option (Option C)) (keys : PK × SK) (x : Σ o, PKEChallenge.Input M C o),
      (PKE.ChallengeCCA.Challenge.freshStep b (PKE.Real.freshStep pke)).outcome
          (cC, (some keys, ((), ()))) x =
        fTransform (Prod.map (fun s => (s.1.map Prod.snd, (s.1.map Prod.fst, ((), ())))) id)
          ((PKE.ChallengeCCA.Game.freshStep pke b).outcome
            (some (keys, cC.getD none), ((), ())) x) := by
    rintro cC keys ⟨_ | _ | _, u⟩
    · obtain ⟨⟩ := u
      rw [PKE.ChallengeCCA.Challenge.outcome_publicKey _ b cC _
          (Finsupp.single ((some keys, ((), ())), keys.1) 1)
          (by rw [PKE.Real.outcome_publicKey, bindK_single, one_smul]),
        bindK_single, one_smul, PKE.ChallengeCCA.Game.outcome_publicKey, fTransform_single]
      rfl
    · obtain ⟨m₀, m₁⟩ := u
      have henc : (PKE.Real.freshStep pke).outcome (some keys, ((), ()))
          ⟨.enc, if b then m₁ else m₀⟩ = bindK (bindK pke.encryptions.1 fun E =>
            Finsupp.single ((some keys, ((), ())), E (keys.1, if b then m₁ else m₀)) 1)
              fun z => Finsupp.single (z.1, ⟨.enc, z.2⟩) 1 := by
        rw [PKE.Real.outcome_enc, bindK_bindK]
        exact bindK_congr fun E _ => by rw [bindK_single, one_smul]
      rcases cC with _ | _ | cs
      · rw [PKE.ChallengeCCA.Challenge.outcome_challenge _ b none rfl _ m₀ m₁ _ henc,
          Option.getD_none, PKE.ChallengeCCA.Game.outcome_challenge, fTransform_bindK,
          bindK_bindK]
        refine bindK_congr fun E _ => ?_
        rw [bindK_single, one_smul, fTransform_single]
        rfl
      · rw [PKE.ChallengeCCA.Challenge.outcome_challenge _ b (some none) rfl _ m₀ m₁ _ henc,
          Option.getD_some, PKE.ChallengeCCA.Game.outcome_challenge, fTransform_bindK,
          bindK_bindK]
        refine bindK_congr fun E _ => ?_
        rw [bindK_single, one_smul, fTransform_single]
        rfl
      · rw [PKE.ChallengeCCA.Challenge.outcome_challenge_some, Option.getD_some,
          PKE.ChallengeCCA.Game.outcome_challenge_some, fTransform_single]
        rfl
    · by_cases hc : cC.getD none = some u
      · obtain rfl : cC = some (some u) := by rcases cC with _ | _ | _ <;> simp_all
        rw [PKE.ChallengeCCA.Challenge.outcome_dec_challenge, Option.getD_some,
          PKE.ChallengeCCA.Game.outcome_dec, if_pos rfl, fTransform_single]
        rfl
      · rw [PKE.ChallengeCCA.Challenge.outcome_dec _ b cC _ u hc
          (Finsupp.single ((some keys, ((), ())), pke.dec keys.2 u) 1)
          (by rw [PKE.Real.outcome_dec, bindK_single, one_smul]),
          PKE.ChallengeCCA.Game.outcome_dec, if_neg hc, bindK_single, one_smul,
          fTransform_single]
        rfl
  refine (PKE.ChallengeCCA.Game.freshSampling pke b q).eq_fresh.trans
    (Eq.trans ?_ (PKE.ChallengeCCA.Challenge.freshSamplingReal pke b q).eq_fresh.symm)
  refine Resource.ofProbAutomaton_eq_of_map _ _ _ _
    (fun s => (s.1.map Prod.snd, (s.1.map Prod.fst, ((), ())))) ?_ ?_ <;>
    dsimp only [PKE.ChallengeCCA.Game.freshSampling, PKE.ChallengeCCA.Challenge.freshSamplingReal,
      FreshSampling.ofProgram, FreshSampling.parallel, FreshSampling.source,
      Distribution.ProbDist.single]
  · rintro ⟨_ | ⟨keys, cs⟩, ⟨⟩, ⟨⟩⟩ x
    · -- Both sample the keys at the first query.
      refine (PKE.ChallengeCCA.Challenge.outcome_bindK (PKE.Real.freshStep pke) b none rfl
        (none, ((), ())) pke.gen.1 (fun keys => (some keys, ((), ())))
          (PKE.Real.outcome_none pke) x).trans ?_
      rw [PKE.ChallengeCCA.Game.outcome_none, fTransform_bindK]
      exact bindK_congr fun keys _ => hsome none keys x
    · exact hsome (some cs) keys x
  · rw [fTransform_single]
    rfl

omit [DecidableEq SK] [DecidableEq K] in
/-- **`IND-CCA^KEM(b)` is the challenge on the public key, `E_pk` and `D_sk`.** -/
lemma KEM.ChallengeCCA.Game.eq_real (kem : KEM PK SK C₁ K) (b : Bool) {q : ℕ} :
    KEM.ChallengeCCA.Game kem b (budget := q) =
      KEM.ChallengeCCA.Challenge PK C₁ K b • KEM.Real kem := by
  -- Once encapsulated, the challenge on `KEM-real` answers as `IND-CCA^KEM(b)`.
  have hsome : ∀ (keys : PK × SK) (k₁ : K) (e : PK → C₁ × K) (x : Σ i, KEMChallenge.Input C₁ i),
      (KEM.ChallengeCCA.Challenge.freshStep b (KEM.Real.freshStep kem)).outcome
          (some (some (keys.1, (e keys.1).1, if b then k₁ else (e keys.1).2)),
            ((some keys, ((), ())), ((), ()))) x =
        fTransform (Prod.map (fun s => (s.1.map fun z =>
            some (z.1.1, (z.2.2 z.1.1).1, if b then z.2.1 else (z.2.2 z.1.1).2),
              ((s.1.map Prod.fst, ((), ())), ((), ())))) id)
          ((KEM.ChallengeCCA.Game.freshStep kem b).outcome
            (some (keys, k₁, e), ((), ((), ()))) x) := by
    rintro keys k₁ e ⟨_ | _, u⟩
    · obtain ⟨⟩ := u
      rw [KEM.ChallengeCCA.Challenge.outcome_input_some, KEM.ChallengeCCA.Game.outcome_input,
        fTransform_single]
      rfl
    · rw [KEM.ChallengeCCA.Challenge.outcome_dec_some _ b _ _ u (kem.decaps keys.2 u)
          (fun _ => KEM.Real.outcome_decaps kem keys u),
        KEM.ChallengeCCA.Game.outcome_dec, fTransform_single]
      rfl
  -- At the first query, the challenge encapsulates through `KEM-real` and samples `k₁`.
  have hinit : ∀ (keys : PK × SK) (x : Σ i, KEMChallenge.Input C₁ i),
      (KEM.ChallengeCCA.Challenge.freshStep b (KEM.Real.freshStep kem)).outcome
          (none, ((some keys, ((), ())), ((), ()))) x =
        bindK (𝒰[K]).1 fun k₁ => bindK kem.encapsulations.1 fun e =>
          fTransform (Prod.map (fun s => (s.1.map fun z =>
              some (z.1.1, (z.2.2 z.1.1).1, if b then z.2.1 else (z.2.2 z.1.1).2),
                ((s.1.map Prod.fst, ((), ())), ((), ())))) id)
            ((KEM.ChallengeCCA.Game.freshStep kem b).outcome
              (some (keys, k₁, e), ((), ((), ()))) x) := by
    rintro keys ⟨_ | _, u⟩
    · obtain ⟨⟩ := u
      rw [KEM.ChallengeCCA.Challenge.outcome_input _ b none rfl _ keys.1
        (KEM.Real.outcome_publicKey kem keys) kem.encapsulations.1 (fun e => e keys.1)
        (KEM.Real.outcome_encaps kem keys), bindK_comm]
      refine bindK_congr fun k₁ _ => bindK_congr fun e _ => ?_
      rw [KEM.ChallengeCCA.Game.outcome_input, fTransform_single]
      rfl
    · rw [KEM.ChallengeCCA.Challenge.outcome_dec _ b none rfl _ keys.1
        (KEM.Real.outcome_publicKey kem keys) kem.encapsulations.1 (fun e => e keys.1)
        (KEM.Real.outcome_encaps kem keys) u (kem.decaps keys.2 u)
        (KEM.Real.outcome_decaps kem keys u), bindK_comm]
      refine bindK_congr fun k₁ _ => bindK_congr fun e _ => ?_
      rw [KEM.ChallengeCCA.Game.outcome_dec, fTransform_single]
      rfl
  refine (KEM.ChallengeCCA.Game.freshSampling kem b q).eq_fresh.trans
    (Eq.trans ?_ (KEM.ChallengeCCA.Challenge.freshSamplingReal kem b q).eq_fresh.symm)
  refine Resource.ofProbAutomaton_eq_of_map _ _ _ _ (fun s => (s.1.map fun z =>
      some (z.1.1, (z.2.2 z.1.1).1, if b then z.2.1 else (z.2.2 z.1.1).2),
        ((s.1.map Prod.fst, ((), ())), ((), ())))) ?_ ?_ <;>
    dsimp only [KEM.ChallengeCCA.Game.freshSampling, KEM.ChallengeCCA.Challenge.freshSamplingReal,
      FreshSampling.ofRightContext, FreshSampling.cast, FreshSampling.ofProgram,
      FreshSampling.parallel, FreshSampling.source, Distribution.ProbDist.single]
  · rintro ⟨_ | ⟨keys, k₁, e⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩ x
    · -- Both sample the keys at the first query.
      refine (KEM.ChallengeCCA.Challenge.outcome_bindK (KEM.Real.freshStep kem) b none rfl
        (none, ((), ())) kem.gen.1 (fun keys => (some keys, ((), ())))
          (KEM.Real.outcome_none kem _) x).trans ?_
      rw [KEM.ChallengeCCA.Game.outcome_none]
      simp only [fTransform_bindK]
      exact bindK_congr fun keys _ => hinit keys x
    · exact hsome keys k₁ e x
  · rw [fTransform_single]
    rfl

end Presentations

/-! ## The sequence of games

Each step of Figure 3 of [1] changes one thing: `G₁(b)` generates the KEM challenge upfront and
decrypts `c₁*` to `k*`, which a perfectly correct KEM does not notice; `B₁ b` interpolates `G₁(b)`
on the real KEM game and `G₂(b)` on the ideal one; `B₂` interpolates `G₂(b)` on the DEM game. -/

omit [DecidableEq SK] [Nonempty K] in
/-- **`IND-CCA^PKE(b) = G₁(b)`** [1, proof of Theorem 1]: for a perfectly correct KEM,
generating the KEM challenge upfront and decrypting `c₁*` to `k*` is not noticeable. -/
theorem game_eq_G₁ (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (correct : kem.Correct) (b : Bool) {q : ℕ} :
    PKE.ChallengeCCA.Game (scheme kem dem) b (budget := q) = G₁ kem dem b := by
  -- Before the challenge, the encapsulations of `G₁(b)` are sampled by the kernel.
  have hI : ∀ keys ∈ kem.gen.1.support, ∀ x : Σ o, PKEChallenge.Input M (C₁ × C₂) o,
      ProbStep.SimulatesAt (PKE.ChallengeCCA.Game.freshStep (scheme kem dem) b)
        (G₁.freshStep kem dem b) (PKE.ChallengeCCA.Game.kernelG₁ kem)
        (some (keys, none), ((), ())) x := by
    intro keys hkeys ⟨o, u⟩
    unfold ProbStep.SimulatesAt
    conv_lhs => dsimp only [PKE.ChallengeCCA.Game.kernelG₁, Distribution.ProbDist.map]
    rw [bindK_fTransform]
    cases o
    · obtain ⟨⟩ := u
      rw [PKE.ChallengeCCA.Game.outcome_publicKey, bindK_single, one_smul]
      dsimp only [PKE.ChallengeCCA.Game.kernelG₁, Distribution.ProbDist.map]
      rw [fTransform_fTransform, fTransform_eq_bindK]
      refine bindK_congr fun e _ => ?_
      exact G₁.outcome_publicKey kem dem b keys e none
    · -- The challenge encapsulation is the encapsulation of `G₁(b)` under `pk`.
      obtain ⟨m₀, m₁⟩ := u
      rw [PKE.ChallengeCCA.Game.outcome_challenge, bindK_bindK]
      simp only [bindK_single, one_smul]
      rw [PublicKeyEncryption.bindK_encryptions (scheme kem dem) keys.1 (if b then m₁ else m₀)
        (fun c => fTransform (fun s₂ => (s₂, (⟨.challenge, some c⟩ :
          Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)))
          (PKE.ChallengeCCA.Game.kernelG₁ kem (some (keys, some c), ((), ()))).1)]
      dsimp only [scheme]
      rw [Distribution.ProbDist.bind_val, bindK_bindK, KEM.encapsulations_eq_bindK kem keys.1,
        bindK_bindK]
      refine bindK_congr fun ck hck => ?_
      have hdk : kem.decaps keys.2 ck.1 = some ck.2 := correct keys.1 keys.2 hkeys ck.1 ck.2 hck
      rw [show (Distribution.ProbDist.map (fun c₂ => (ck.1, c₂)) (dem.enc ck.2
        (if b then m₁ else m₀))).1 = fTransform (fun c₂ => (ck.1, c₂))
          (dem.enc ck.2 (if b then m₁ else m₀)).1 from rfl, bindK_fTransform]
      calc _ = bindK (KEM.encapsulationsGiven kem keys.1 ck).1 fun e =>
            bindK (dem.enc ck.2 (if b then m₁ else m₀)).1 fun c₂ =>
              Finsupp.single ((some (keys, e, some (ck.1, c₂)), ((), ((), ()))),
                (⟨.challenge, some (ck.1, c₂)⟩ : Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1 :=
          bindK_congr fun e he => by
            refine (G₁.outcome_challenge kem dem b keys e m₀ m₁).trans ?_
            rw [SymmetricEncryption.bindK_encryptions dem (e keys.1).2 (if b then m₁ else m₀)
              (fun c₂ => Finsupp.single ((some (keys, e, some ((e keys.1).1, c₂)),
                ((), ((), ()))), (⟨.challenge, some ((e keys.1).1, c₂)⟩ :
                  Σ o, PKEChallenge.Output PK M (C₁ × C₂) o)) 1),
              KEM.apply_of_mem_support_encapsulationsGiven he]
        _ = _ := by
          rw [bindK_comm]
          refine bindK_congr fun c₂ _ => ?_
          simp only [Function.comp_apply, PKE.ChallengeCCA.Game.kernelG₁, hdk,
            Distribution.ProbDist.map, fTransform_eq_bindK, bindK_bindK, bindK_single, one_smul,
            Prod.mk.eta]
    · -- Decapsulating `c₁*` gives the encapsulated key, by correctness.
      rw [PKE.ChallengeCCA.Game.outcome_dec, bindK_single, one_smul]
      dsimp only [PKE.ChallengeCCA.Game.kernelG₁, Distribution.ProbDist.map]
      rw [fTransform_fTransform, fTransform_eq_bindK]
      refine bindK_congr fun e he => (G₁.outcome_dec kem dem b keys e none u).trans ?_
      have hdk : kem.decaps keys.2 (e keys.1).1 = some (e keys.1).2 :=
        correct keys.1 keys.2 hkeys _ _ (Distribution.ProbDist.mem_support_pi (μ := kem.encaps) he
          keys.1)
      by_cases h₂ : u.1 = (e keys.1).1
      · simp [scheme, h₂, hdk]
      · simp [scheme, h₂]
  -- After the challenge, the encapsulation of `G₁(b)` under `pk` is the challenge one.
  have hII : ∀ keys ∈ kem.gen.1.support, ∀ (c : C₁ × C₂) (k : K),
      (c.1, k) ∈ (kem.encaps keys.1).1.support → ∀ x : Σ o, PKEChallenge.Input M (C₁ × C₂) o,
      ProbStep.SimulatesAt (PKE.ChallengeCCA.Game.freshStep (scheme kem dem) b)
        (G₁.freshStep kem dem b) (PKE.ChallengeCCA.Game.kernelG₁ kem)
        (some (keys, some c), ((), ())) x := by
    intro keys hkeys c k hk ⟨o, u⟩
    have hdk : kem.decaps keys.2 c.1 = some k := correct keys.1 keys.2 hkeys c.1 k hk
    unfold ProbStep.SimulatesAt
    conv_lhs => simp only [PKE.ChallengeCCA.Game.kernelG₁, hdk, Distribution.ProbDist.map]
    rw [bindK_fTransform]
    cases o
    · obtain ⟨⟩ := u
      rw [PKE.ChallengeCCA.Game.outcome_publicKey, bindK_single, one_smul]
      simp only [PKE.ChallengeCCA.Game.kernelG₁, hdk, Distribution.ProbDist.map]
      rw [fTransform_fTransform, fTransform_eq_bindK]
      refine bindK_congr fun e _ => ?_
      exact G₁.outcome_publicKey kem dem b keys e (some c)
    · obtain ⟨m₀, m₁⟩ := u
      rw [PKE.ChallengeCCA.Game.outcome_challenge_some, bindK_single, one_smul]
      simp only [PKE.ChallengeCCA.Game.kernelG₁, hdk, Distribution.ProbDist.map]
      rw [fTransform_fTransform, fTransform_eq_bindK]
      refine bindK_congr fun e _ => ?_
      exact G₁.outcome_challenge_some kem dem b keys e c m₀ m₁
    · rw [PKE.ChallengeCCA.Game.outcome_dec, bindK_single, one_smul]
      simp only [PKE.ChallengeCCA.Game.kernelG₁, hdk, Distribution.ProbDist.map]
      rw [fTransform_fTransform, fTransform_eq_bindK]
      refine bindK_congr fun e he => (G₁.outcome_dec kem dem b keys e (some c) u).trans ?_
      rw [KEM.apply_of_mem_support_encapsulationsGiven he]
      by_cases h₁ : some c = some u
      · simp [h₁]
      by_cases h₂ : u.1 = c.1
      · simp [scheme, h₁, h₂, hdk]
      · simp [scheme, h₁, h₂]
  -- The invariant holds after each step.
  have presI : ∀ keys ∈ kem.gen.1.support, ∀ (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o) p,
      p ∈ ((PKE.ChallengeCCA.Game.freshStep (scheme kem dem) b).outcome
        (some (keys, none), ((), ())) x).support →
      PKE.ChallengeCCA.Game.Encapsulated kem p.1 := by
    intro keys hkeys ⟨o, u⟩ p hp
    cases o
    · obtain ⟨⟩ := u
      rw [PKE.ChallengeCCA.Game.outcome_publicKey] at hp
      rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
      exact ⟨hkeys, fun c hc => absurd hc (by simp)⟩
    · obtain ⟨m₀, m₁⟩ := u
      rw [PKE.ChallengeCCA.Game.outcome_challenge] at hp
      obtain ⟨E, hE, hp⟩ := mem_support_bindK hp
      rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
      refine ⟨hkeys, fun c hc => ?_⟩
      obtain rfl := Option.some_injective _ hc
      have hc' := Distribution.ProbDist.mem_support_pi
        (μ := fun pm : PK × M => (scheme kem dem).enc pm.1 pm.2) hE (keys.1, if b then m₁ else m₀)
      obtain ⟨ck, hck, hc'⟩ := Distribution.ProbDist.mem_support_bind hc'
      obtain ⟨c₂, -, hc₂⟩ := Distribution.ProbDist.mem_support_map hc'
      exact ⟨ck.2, by rw [← hc₂]; exact hck⟩
    · rw [PKE.ChallengeCCA.Game.outcome_dec] at hp
      rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
      exact ⟨hkeys, fun c hc => absurd hc (by simp)⟩
  have presII : ∀ keys ∈ kem.gen.1.support, ∀ (c : C₁ × C₂) (k : K),
      (c.1, k) ∈ (kem.encaps keys.1).1.support → ∀ (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o) p,
      p ∈ ((PKE.ChallengeCCA.Game.freshStep (scheme kem dem) b).outcome
        (some (keys, some c), ((), ())) x).support →
      PKE.ChallengeCCA.Game.Encapsulated kem p.1 := by
    intro keys hkeys c k hk ⟨o, u⟩ p hp
    have hinv : PKE.ChallengeCCA.Game.Encapsulated kem (some (keys, some c), ((), ())) :=
      ⟨hkeys, fun c' hc' => ⟨k, by rw [← Option.some_injective _ hc']; exact hk⟩⟩
    cases o
    · obtain ⟨⟩ := u
      rw [PKE.ChallengeCCA.Game.outcome_publicKey] at hp
      rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
      exact hinv
    · obtain ⟨m₀, m₁⟩ := u
      rw [PKE.ChallengeCCA.Game.outcome_challenge_some] at hp
      rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
      exact hinv
    · rw [PKE.ChallengeCCA.Game.outcome_dec] at hp
      rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
      exact hinv
  refine (PKE.ChallengeCCA.Game.freshSampling (scheme kem dem) b q).eq_fresh.trans
    (Eq.trans ?_ (G₁.freshSampling kem dem b q).eq_fresh.symm)
  refine Interface.Resource.ofProbAutomaton_eq_of_simulation _ _ _ _
    (PKE.ChallengeCCA.Game.kernelG₁ kem) (fun _ s => PKE.ChallengeCCA.Game.Encapsulated kem s)
    ?_ ?_ ?_ ?_ <;>
    dsimp only [PKE.ChallengeCCA.Game.freshSampling, G₁.freshSampling, FreshSampling.ofProgram,
      FreshSampling.parallel, FreshSampling.source, id, Distribution.ProbDist.single]
  · intro s hs
    rw [((Finsupp.mem_support_single _ _ _).mp hs).1]
    exact trivial
  · rintro xs ⟨_ | ⟨keys, _ | c⟩, ⟨⟩, ⟨⟩⟩ x hinv - p hp
    · rw [PKE.ChallengeCCA.Game.outcome_none] at hp
      obtain ⟨keys, hkeys, hp⟩ := mem_support_bindK hp
      exact presI keys hkeys x p hp
    · exact presI keys hinv.1 x p hp
    · obtain ⟨k, hk⟩ := hinv.2 c rfl
      exact presII keys hinv.1 c k hk x p hp
  · rintro xs ⟨_ | ⟨keys, _ | c⟩, ⟨⟩, ⟨⟩⟩ x hinv -
    · -- Both generate the keys, then step as before the challenge.
      unfold ProbStep.SimulatesAt
      conv_lhs => dsimp only [PKE.ChallengeCCA.Game.kernelG₁, Distribution.ProbDist.single]
      rw [bindK_single, one_smul, PKE.ChallengeCCA.Game.outcome_none, bindK_bindK]
      refine (G₁.outcome_none kem dem b x).trans (bindK_congr fun keys hkeys => ?_)
      refine Eq.trans ?_ (hI keys hkeys x)
      dsimp only [PKE.ChallengeCCA.Game.kernelG₁, Distribution.ProbDist.map]
      rw [bindK_fTransform]
      rfl
    · exact hI keys hinv.1 x
    · obtain ⟨k, hk⟩ := hinv.2 c rfl
      exact hII keys hinv.1 c k hk x
  · rw [bindK_single, one_smul]
    rfl

omit [Nonempty K] in
/-- **The first step up to the correctness error** [1, §3.1]: `IND-CCA^PKE(b)` and `G₁(b)` are
identical until `KEM.Dec(sk, c₁*) ≠ k*`, an event of the key generation and the challenge
encapsulation alone, of probability at most `δ`. -/
theorem game_G₁_distance_le (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (δ : ℝ)
    (correctnessError : kem.CorrectnessError δ) (b : Bool) {q : ℕ} :
    Δ (PKE.ChallengeCCA.Game (scheme kem dem) b (budget := q)) (G₁ kem dem b) ≤
      ENNReal.ofReal δ := by
  rw [PKE.ChallengeCCA.Game.eq_sample kem dem b, G₁.eq_sample kem dem b]
  exact (Interface.Resource.distance_sample_le _ _ _
    (fun z => kem.decaps z.1.2 (z.2 z.1.1).1 ≠ some (z.2 z.1.1).2) fun z _ hz =>
      (G₁.eq_upfront kem dem b z (not_not.mp hz)).symm).trans
    (ENNReal.ofReal_le_ofReal (KEM.mass_encapsulations_le kem δ correctnessError))

omit [DecidableEq SK] in
/-- **`G₁(b) = B₁ b • IND-CCA^KEM(0)`** [1, proof of Theorem 1]: on the real KEM game, `B₁ b`
is `G₁(b)`. -/
theorem G₁_eq_B₁ (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (b : Bool) {q : ℕ} :
    G₁ kem dem b (budget := q) = B₁ PK C₁ dem b • KEM.ChallengeCCA.Game kem false := by
  -- Once `IND-CCA^KEM(0)` is initialized, `B₁ b` on it steps as `G₁(b)`.
  have hsome : ∀ (cB : Option (Option (C₁ × C₂))) (keys : PK × SK) (k₁ : K) (e : PK → C₁ × K)
      (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o),
      (G₁.freshStep kem dem b).outcome (some (keys, e, cB.getD none), ((), ((), ()))) x =
        fTransform (Prod.map B₁.stateG₁ id)
          ((B₁.freshStep dem b (KEM.ChallengeCCA.Game.freshStep kem false)).outcome
            (cB, ((some (keys, k₁, e), ((), ((), ()))), ())) x) := by
    intro cB keys k₁ e ⟨o, u⟩
    have hin := KEM.ChallengeCCA.Game.outcome_input kem false keys k₁ e
    cases o
    · obtain ⟨⟩ := u
      rw [G₁.outcome_publicKey, B₁.outcome_publicKey _ dem b cB _ _ hin, fTransform_single]
      rfl
    · obtain ⟨m₀, m₁⟩ := u
      rcases cB with _ | _ | cs
      · rw [Option.getD_none, G₁.outcome_challenge, B₁.outcome_challenge _ dem b none rfl _ _ hin,
          fTransform_bindK]
        refine bindK_congr fun E _ => ?_
        rw [fTransform_single]
        rfl
      · rw [Option.getD_some, G₁.outcome_challenge,
          B₁.outcome_challenge _ dem b (some none) rfl _ _ hin, fTransform_bindK]
        refine bindK_congr fun E _ => ?_
        rw [fTransform_single]
        rfl
      · rw [Option.getD_some, G₁.outcome_challenge_some,
          B₁.outcome_challenge_some _ dem b _ _ _ hin, fTransform_single]
        rfl
    · rw [G₁.outcome_dec, B₁.outcome_dec _ dem b cB _ _ hin (kem.decaps keys.2)
        (fun c₁ h => by rw [KEM.ChallengeCCA.Game.outcome_dec, if_neg h]), fTransform_single]
      rfl
  refine (G₁.freshSampling kem dem b q).eq_fresh.trans
    (Eq.trans ?_ (B₁.freshSamplingKEM kem dem b false q).eq_fresh.symm)
  symm
  refine Interface.Resource.ofProbAutomaton_eq_of_mapOn _ _ _ _ B₁.stateG₁
    (fun s => s.2.1.1 = none → s.1 = none) ?_ (B₁.initKEM_pres kem dem b false) ?_ ?_ <;>
    dsimp only [G₁.freshSampling, B₁.freshSamplingKEM, KEM.ChallengeCCA.Game.freshSampling,
      FreshSampling.ofRightContext, FreshSampling.cast, FreshSampling.ofProgram,
      FreshSampling.parallel, FreshSampling.source, id, Distribution.ProbDist.single]
  · intro s hs _
    rw [((Finsupp.mem_support_single _ _ _).mp hs).1]
  · rintro ⟨cB, ⟨_ | ⟨keys, k₁, e⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩ x hs
    · -- Both initialize; `k₁` is not used.
      obtain rfl : cB = none := hs rfl
      refine (G₁.outcome_none kem dem b x).trans ?_
      rw [B₁.outcome_initKEM]
      simp only [fTransform_bindK]
      refine bindK_congr fun keys _ => ?_
      refine (bindK_const_of_weight (𝒰[K]).2.2 _).symm.trans
        (bindK_congr fun k₁ _ => bindK_congr fun e _ => ?_)
      exact hsome none keys k₁ e x
    · exact hsome cB keys k₁ e x
  · rw [fTransform_single]
    rfl

omit [DecidableEq SK] in
/-- **`G₂(b) = B₁ b • IND-CCA^KEM(1)`** [1, proof of Theorem 1]: on the ideal KEM game, `B₁ b`
is `G₂(b)`. -/
theorem G₂_eq_B₁ (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (b : Bool) {q : ℕ} :
    G₂ kem dem b (budget := q) = B₁ PK C₁ dem b • KEM.ChallengeCCA.Game kem true := by
  -- Once `IND-CCA^KEM(1)` is initialized, `B₁ b` on it steps as `G₂(b)` with `k* = k₁`.
  have hsome : ∀ (cB : Option (Option (C₁ × C₂))) (keys : PK × SK) (k₁ : K) (e : PK → C₁ × K)
      (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o),
      (G₂.freshStep kem dem b).outcome (some (keys, e, k₁, cB.getD none), ((), ((), ((), ())))) x =
        fTransform (Prod.map B₁.stateG₂ id)
          ((B₁.freshStep dem b (KEM.ChallengeCCA.Game.freshStep kem true)).outcome
            (cB, ((some (keys, k₁, e), ((), ((), ()))), ())) x) := by
    intro cB keys k₁ e ⟨o, u⟩
    have hin := KEM.ChallengeCCA.Game.outcome_input kem true keys k₁ e
    cases o
    · obtain ⟨⟩ := u
      rw [G₂.outcome_publicKey, B₁.outcome_publicKey _ dem b cB _ _ hin, fTransform_single]
      rfl
    · obtain ⟨m₀, m₁⟩ := u
      rcases cB with _ | _ | cs
      · rw [Option.getD_none, G₂.outcome_challenge, B₁.outcome_challenge _ dem b none rfl _ _ hin,
          fTransform_bindK]
        refine bindK_congr fun E _ => ?_
        rw [fTransform_single]
        rfl
      · rw [Option.getD_some, G₂.outcome_challenge,
          B₁.outcome_challenge _ dem b (some none) rfl _ _ hin, fTransform_bindK]
        refine bindK_congr fun E _ => ?_
        rw [fTransform_single]
        rfl
      · rw [Option.getD_some, G₂.outcome_challenge_some,
          B₁.outcome_challenge_some _ dem b _ _ _ hin, fTransform_single]
        rfl
    · rw [G₂.outcome_dec, B₁.outcome_dec _ dem b cB _ _ hin (kem.decaps keys.2)
        (fun c₁ h => by rw [KEM.ChallengeCCA.Game.outcome_dec, if_neg h]), fTransform_single]
      rfl
  refine (G₂.freshSampling kem dem b q).eq_fresh.trans
    (Eq.trans ?_ (B₁.freshSamplingKEM kem dem b true q).eq_fresh.symm)
  symm
  refine Interface.Resource.ofProbAutomaton_eq_of_mapOn _ _ _ _ B₁.stateG₂
    (fun s => s.2.1.1 = none → s.1 = none) ?_ (B₁.initKEM_pres kem dem b true) ?_ ?_ <;>
    dsimp only [G₂.freshSampling, B₁.freshSamplingKEM, KEM.ChallengeCCA.Game.freshSampling,
      FreshSampling.ofRightContext, FreshSampling.cast, FreshSampling.ofProgram,
      FreshSampling.parallel, FreshSampling.source, id, Distribution.ProbDist.single]
  · intro s hs _
    rw [((Finsupp.mem_support_single _ _ _).mp hs).1]
  · rintro ⟨cB, ⟨_ | ⟨keys, k₁, e⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩ x hs
    · -- Both initialize; `k*` and `k₁` are sampled in a different order.
      obtain rfl : cB = none := hs rfl
      refine (G₂.outcome_none kem dem b x).trans ?_
      rw [B₁.outcome_initKEM]
      simp only [fTransform_bindK]
      refine bindK_congr fun keys _ => ?_
      refine (bindK_comm _ _ _).trans (bindK_congr fun k₁ _ => bindK_congr fun e _ => ?_)
      exact hsome none keys k₁ e x
    · exact hsome cB keys k₁ e x
  · rw [fTransform_single]
    rfl

omit [DecidableEq SK] in
/-- **`G₂(b) = B₂ • IND-CCA^DEM(b)`** [1, proof of Theorem 1]: on the DEM game, `B₂` is
`G₂(b)`. -/
theorem G₂_eq_B₂ (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂) (b : Bool) {q : ℕ} :
    G₂ kem dem b (budget := q) = B₂ M C₂ kem dem • DEM.ChallengeCCA.Game dem b := by
  -- Before `IND-CCA^DEM(b)` is initialized, `k*` is sampled by the kernel.
  have hB : ∀ (keys : PK × SK) (e : PK → C₁ × K) (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o),
      ProbStep.SimulatesAt (B₂.freshStepDEM kem dem b) (G₂.freshStep kem dem b) B₂.kernelG₂
        (some (keys, e, none), ((none, ((), ())), ((), ()))) x := by
    intro keys e ⟨o, u⟩
    unfold ProbStep.SimulatesAt
    conv_lhs => dsimp only [B₂.kernelG₂, Distribution.ProbDist.map]
    rw [bindK_fTransform]
    cases o
    · obtain ⟨⟩ := u
      rw [B₂.outcome_publicKey_DEM, bindK_single, one_smul]
      dsimp only [B₂.kernelG₂, Distribution.ProbDist.map]
      rw [fTransform_fTransform, fTransform_eq_bindK]
      refine bindK_congr fun k _ => ?_
      exact G₂.outcome_publicKey kem dem b keys e k none
    · obtain ⟨m₀, m₁⟩ := u
      rw [B₂.outcome_challenge_DEM_none]
      simp only [bindK_bindK, bindK_single, one_smul]
      refine bindK_congr fun k _ => (G₂.outcome_challenge kem dem b keys e k m₀ m₁).trans ?_
      refine bindK_congr fun E _ => ?_
      dsimp only [B₂.kernelG₂, Distribution.ProbDist.single]
      rw [fTransform_single]
    · by_cases h₂ : u.1 = (e keys.1).1
      · rw [B₂.outcome_dec_DEM_none kem dem b keys e none u (by simp) h₂]
        simp only [bindK_bindK, bindK_single, one_smul]
        refine bindK_congr fun k _ => (G₂.outcome_dec kem dem b keys e k none u).trans ?_
        dsimp only [B₂.kernelG₂, Distribution.ProbDist.single]
        rw [fTransform_single]
        simp [h₂]
      · rw [B₂.outcome_dec_other kem dem b keys e none none u (Or.inr h₂), bindK_single,
          one_smul]
        dsimp only [B₂.kernelG₂, Distribution.ProbDist.map]
        rw [fTransform_fTransform, fTransform_eq_bindK]
        refine bindK_congr fun k _ => (G₂.outcome_dec kem dem b keys e k none u).trans ?_
        simp [h₂]
  -- Once `IND-CCA^DEM(b)` is initialized, `k*` is its key.
  have hA : ∀ (keys : PK × SK) (e : PK → C₁ × K) (k : K) (cd : Option C₂)
      (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o),
      ProbStep.SimulatesAt (B₂.freshStepDEM kem dem b) (G₂.freshStep kem dem b) B₂.kernelG₂
        (some (keys, e, cd.map fun c₂ => ((e keys.1).1, c₂)), ((some (k, cd), ((), ())), ((), ())))
        x := by
    intro keys e k cd ⟨o, u⟩
    unfold ProbStep.SimulatesAt
    conv_lhs => dsimp only [B₂.kernelG₂, Distribution.ProbDist.single]
    rw [bindK_single, one_smul]
    cases o
    · obtain ⟨⟩ := u
      rw [B₂.outcome_publicKey_DEM, bindK_single, one_smul]
      dsimp only [B₂.kernelG₂, Distribution.ProbDist.single]
      rw [fTransform_single]
      exact G₂.outcome_publicKey kem dem b keys e k _
    · obtain ⟨m₀, m₁⟩ := u
      cases cd with
      | none =>
        rw [B₂.outcome_challenge_DEM]
        simp only [bindK_bindK, bindK_single, one_smul, Option.map_none]
        refine (G₂.outcome_challenge kem dem b keys e k m₀ m₁).trans (bindK_congr fun E _ => ?_)
        dsimp only [B₂.kernelG₂, Distribution.ProbDist.single]
        rw [fTransform_single]
      | some c₂ =>
        rw [B₂.outcome_challenge_DEM_some, bindK_single, one_smul]
        dsimp only [B₂.kernelG₂, Distribution.ProbDist.single]
        rw [fTransform_single, Option.map_some]
        exact G₂.outcome_challenge_some kem dem b keys e k _ m₀ m₁
    · by_cases h₁ : (cd.map fun c₂ => ((e keys.1).1, c₂)) = some u
      · rw [B₂.outcome_dec_other kem dem b keys e _ _ u (Or.inl h₁), bindK_single, one_smul]
        dsimp only [B₂.kernelG₂, Distribution.ProbDist.single]
        rw [fTransform_single]
        refine (G₂.outcome_dec kem dem b keys e k _ u).trans ?_
        simp [h₁]
      by_cases h₂ : u.1 = (e keys.1).1
      · have hcd : cd ≠ some u.2 := fun h => h₁ (by rw [h, Option.map_some, ← h₂])
        rw [B₂.outcome_dec_DEM kem dem b keys e _ k cd u h₁ h₂, bindK_single, one_smul]
        dsimp only [B₂.kernelG₂, Distribution.ProbDist.single]
        rw [fTransform_single]
        refine (G₂.outcome_dec kem dem b keys e k _ u).trans ?_
        simp [h₁, h₂, hcd]
      · rw [B₂.outcome_dec_other kem dem b keys e _ _ u (Or.inr h₂), bindK_single, one_smul]
        dsimp only [B₂.kernelG₂, Distribution.ProbDist.single]
        rw [fTransform_single]
        refine (G₂.outcome_dec kem dem b keys e k _ u).trans ?_
        simp [h₁, h₂]
  -- The invariant holds after each step.
  have presB : ∀ (keys : PK × SK) (e : PK → C₁ × K) (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o) p,
      p ∈ ((B₂.freshStepDEM kem dem b).outcome
        (some (keys, e, none), ((none, ((), ())), ((), ()))) x).support →
      B₂.ChallengeAgrees p.1 := by
    intro keys e ⟨o, u⟩ p hp
    cases o
    · obtain ⟨⟩ := u
      rw [B₂.outcome_publicKey_DEM] at hp
      rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
      exact rfl
    · obtain ⟨m₀, m₁⟩ := u
      rw [B₂.outcome_challenge_DEM_none] at hp
      obtain ⟨k, -, hp⟩ := mem_support_bindK hp
      obtain ⟨E, -, hp⟩ := mem_support_bindK hp
      rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
      exact rfl
    · by_cases h₂ : u.1 = (e keys.1).1
      · rw [B₂.outcome_dec_DEM_none kem dem b keys e none u (by simp) h₂] at hp
        obtain ⟨k, -, hp⟩ := mem_support_bindK hp
        rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
        exact rfl
      · rw [B₂.outcome_dec_other kem dem b keys e none none u (Or.inr h₂)] at hp
        rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
        exact rfl
  have presA : ∀ (keys : PK × SK) (e : PK → C₁ × K) (k : K) (cd : Option C₂)
      (x : Σ o, PKEChallenge.Input M (C₁ × C₂) o) p,
      p ∈ ((B₂.freshStepDEM kem dem b).outcome
        (some (keys, e, cd.map fun c₂ => ((e keys.1).1, c₂)), ((some (k, cd), ((), ())), ((), ())))
          x).support → B₂.ChallengeAgrees p.1 := by
    intro keys e k cd ⟨o, u⟩ p hp
    cases o
    · obtain ⟨⟩ := u
      rw [B₂.outcome_publicKey_DEM] at hp
      rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
      exact rfl
    · obtain ⟨m₀, m₁⟩ := u
      cases cd with
      | none =>
        rw [B₂.outcome_challenge_DEM] at hp
        obtain ⟨E, -, hp⟩ := mem_support_bindK hp
        rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
        exact rfl
      | some c₂ =>
        rw [B₂.outcome_challenge_DEM_some] at hp
        rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
        exact rfl
    · by_cases h₁ : (cd.map fun c₂ => ((e keys.1).1, c₂)) = some u
      · rw [B₂.outcome_dec_other kem dem b keys e _ _ u (Or.inl h₁)] at hp
        rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
        exact rfl
      by_cases h₂ : u.1 = (e keys.1).1
      · rw [B₂.outcome_dec_DEM kem dem b keys e _ k cd u h₁ h₂] at hp
        rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
        exact rfl
      · rw [B₂.outcome_dec_other kem dem b keys e _ _ u (Or.inr h₂)] at hp
        rw [((Finsupp.mem_support_single _ _ _).mp hp).1]
        exact rfl
  refine (G₂.freshSampling kem dem b q).eq_fresh.trans
    (Eq.trans ?_ (B₂.freshSamplingDEM kem dem b q).eq_fresh.symm)
  symm
  refine Interface.Resource.ofProbAutomaton_eq_of_simulation _ _ _ _ B₂.kernelG₂
    (fun _ s => B₂.ChallengeAgrees s) ?_ ?_ ?_ ?_ <;>
    dsimp only [G₂.freshSampling, B₂.freshSamplingDEM, DEM.ChallengeCCA.Game.freshSampling,
      FreshSampling.ofRightContext, FreshSampling.cast, FreshSampling.ofProgram,
      FreshSampling.parallel, FreshSampling.source, id, Distribution.ProbDist.single]
  · intro s hs
    rw [((Finsupp.mem_support_single _ _ _).mp hs).1]
    exact rfl
  · rintro xs ⟨_ | ⟨keys, e, cs⟩, ⟨_ | ⟨k, cd⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩ x hinv - p hp
    · rw [B₂.outcome_initDEM] at hp
      obtain ⟨keys, -, hp⟩ := mem_support_bindK hp
      obtain ⟨e, -, hp⟩ := mem_support_bindK hp
      exact presB keys e x p hp
    · exact absurd hinv (by simp [B₂.ChallengeAgrees])
    · obtain rfl : cs = none := hinv
      exact presB keys e x p hp
    · obtain rfl : cs = cd.map fun c₂ => ((e keys.1).1, c₂) := hinv
      exact presA keys e k cd x p hp
  · rintro xs ⟨_ | ⟨keys, e, cs⟩, ⟨_ | ⟨k, cd⟩, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩ x hinv -
    · -- `B₂` initializes, then steps as before the DEM game is initialized.
      unfold ProbStep.SimulatesAt
      conv_lhs => dsimp only [B₂.kernelG₂, Distribution.ProbDist.single]
      rw [bindK_single, one_smul, B₂.outcome_initDEM, bindK_bindK]
      refine (G₂.outcome_none kem dem b x).trans (bindK_congr fun keys _ => ?_)
      rw [bindK_bindK]
      refine bindK_congr fun e _ => Eq.trans ?_ (hB keys e x)
      dsimp only [B₂.kernelG₂, Distribution.ProbDist.map]
      rw [bindK_fTransform]
      rfl
    · exact absurd hinv (by simp [B₂.ChallengeAgrees])
    · obtain rfl : cs = none := hinv
      exact hB keys e x
    · obtain rfl : cs = cd.map fun c₂ => ((e keys.1).1, c₂) := hinv
      exact hA keys e k cd x
  · rw [bindK_single, one_smul]
    rfl

omit [DecidableEq SK] in
/-- **The KEM and DEM swaps**: `G₁(0) ≃ G₂(0) ≃ G₂(1) ≃ G₁(1)`, through `B₁ 0`, `B₂` and
`B₁ 1`. -/
lemma G₁_substitutes [AdmissibleDistinguishers] (kem : KEM PK SK C₁ K)
    (dem : SymmetricEncryption K M C₂) {q : ℕ}
    (εkem :
      (KEMChallenge PK C₁ K (B₁.bound PK C₁ dem false * q)).inputDomain.DistinguisherBehavior →
        ENNReal)
    (εdem :
      (ChallengeLeftRight M C₂ (B₂.bound M C₂ kem dem * q)).inputDomain.DistinguisherBehavior →
        ENNReal)
    (kemSecure : KEM.ChallengeCCA kem εkem) (demSecure : DEM.ChallengeCCA dem εdem) :
    G₁ kem dem false (budget := q) ≃[fun D =>
        εkem (absorb (B₁ PK C₁ dem false) D) + εdem (absorb (B₂ M C₂ kem dem) D) +
          εkem (absorb (B₁ PK C₁ dem true) D)] G₁ kem dem true := by
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    G₁ kem dem false (budget := q) = B₁ PK C₁ dem false • KEM.ChallengeCCA.Game kem false :=
      G₁_eq_B₁ kem dem false
    _ = B₁ PK C₁ dem false • (KEM.ChallengeCCA.Challenge PK C₁ K false • KEM.Real kem) := by
      rw [KEM.ChallengeCCA.Game.eq_real]
    _ ≃[εkem ∘ absorb (B₁ PK C₁ dem false)]
        B₁ PK C₁ dem false • (KEM.ChallengeCCA.Challenge PK C₁ K true • KEM.Real kem) :=
      AdmissibleDistinguishers.substitutesWithin_attach _ kemSecure
    _ = B₁ PK C₁ dem false • KEM.ChallengeCCA.Game kem true := by
      rw [KEM.ChallengeCCA.Game.eq_real]
    _ = G₂ kem dem false := (G₂_eq_B₁ kem dem false).symm
    _ = B₂ M C₂ kem dem • DEM.ChallengeCCA.Game dem false := G₂_eq_B₂ kem dem false
    _ = B₂ M C₂ kem dem •
        (DEM.ChallengeCCA.Challenge M C₂ false • AE.Real { dem with gen := 𝒰[K] }) := by
      rw [DEM.ChallengeCCA.Game.eq_real]
    _ ≃[εdem ∘ absorb (B₂ M C₂ kem dem)]
        B₂ M C₂ kem dem •
          (DEM.ChallengeCCA.Challenge M C₂ true • AE.Real { dem with gen := 𝒰[K] }) :=
      AdmissibleDistinguishers.substitutesWithin_attach _ demSecure
    _ = B₂ M C₂ kem dem • DEM.ChallengeCCA.Game dem true := by
      rw [DEM.ChallengeCCA.Game.eq_real]
    _ = G₂ kem dem true := (G₂_eq_B₂ kem dem true).symm
    _ = B₁ PK C₁ dem true • KEM.ChallengeCCA.Game kem true := G₂_eq_B₁ kem dem true
    _ = B₁ PK C₁ dem true • (KEM.ChallengeCCA.Challenge PK C₁ K true • KEM.Real kem) := by
      rw [KEM.ChallengeCCA.Game.eq_real]
    _ ≃[εkem ∘ absorb (B₁ PK C₁ dem true)]
        B₁ PK C₁ dem true • (KEM.ChallengeCCA.Challenge PK C₁ K false • KEM.Real kem) :=
      AdmissibleDistinguishers.substitutesWithin_attach _
        (DistinguisherAdvantage.SubstitutesWithin.symm _ kemSecure)
    _ = B₁ PK C₁ dem true • KEM.ChallengeCCA.Game kem false := by
      rw [KEM.ChallengeCCA.Game.eq_real]
    _ = G₁ kem dem true := (G₁_eq_B₁ kem dem true).symm

omit [DecidableEq SK] in
/-- **Theorem 1** of [1]: if the KEM is perfectly correct, IND-CCA of the KEM within `εkem` and of
the DEM within `εdem` give IND-CCA of KEM + DEM within the losses at `B₁ 0`, `B₁ 1` and `B₂`. -/
theorem kem_dem_cca [AdmissibleDistinguishers] (kem : KEM PK SK C₁ K)
    (dem : SymmetricEncryption K M C₂) (correct : kem.Correct) {q : ℕ}
    (εkem :
      (KEMChallenge PK C₁ K (B₁.bound PK C₁ dem false * q)).inputDomain.DistinguisherBehavior →
        ENNReal)
    (εdem :
      (ChallengeLeftRight M C₂ (B₂.bound M C₂ kem dem * q)).inputDomain.DistinguisherBehavior →
        ENNReal)
    (kemSecure : KEM.ChallengeCCA kem εkem) (demSecure : DEM.ChallengeCCA dem εdem) :
    PKE.ChallengeCCA (scheme kem dem) (q := q) fun D =>
      εkem (absorb (B₁ PK C₁ dem false) D) + εkem (absorb (B₁ PK C₁ dem true) D) +
        εdem (absorb (B₂ M C₂ kem dem) D) := by
  have chain := by
    cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
        (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
      (PKE.ChallengeCCA.Challenge PK M (C₁ × C₂) false • PKE.Real (scheme kem dem) :
          Resource (PKEChallenge PK M (C₁ × C₂) q)) =
          PKE.ChallengeCCA.Game (scheme kem dem) false (budget := q) :=
        (PKE.ChallengeCCA.Game.eq_real (scheme kem dem) false).symm
      _ = G₁ kem dem false := game_eq_G₁ kem dem correct false
      _ ≃[_] G₁ kem dem true := G₁_substitutes kem dem εkem εdem kemSecure demSecure
      _ = PKE.ChallengeCCA.Game (scheme kem dem) true := (game_eq_G₁ kem dem correct true).symm
      _ = PKE.ChallengeCCA.Challenge PK M (C₁ × C₂) true • PKE.Real (scheme kem dem) :=
        PKE.ChallengeCCA.Game.eq_real (scheme kem dem) true
  -- The losses in the order of [1].
  exact fun D hD => (chain D hD).trans_eq (add_right_comm _ _ _)

/-- **Imperfect correctness** [1, §3.1]: with a correctness error of at most `δ`, Theorem 1 holds
with `2δ` more, for the bad event of the first step at each value of the bit. -/
theorem kem_dem_cca_of_correctnessError [AdmissibleDistinguishers] (kem : KEM PK SK C₁ K)
    (dem : SymmetricEncryption K M C₂) (δ : ℝ) (correctnessError : kem.CorrectnessError δ)
    {q : ℕ}
    (εkem :
      (KEMChallenge PK C₁ K (B₁.bound PK C₁ dem false * q)).inputDomain.DistinguisherBehavior →
        ENNReal)
    (εdem :
      (ChallengeLeftRight M C₂ (B₂.bound M C₂ kem dem * q)).inputDomain.DistinguisherBehavior →
        ENNReal)
    (kemSecure : KEM.ChallengeCCA kem εkem) (demSecure : DEM.ChallengeCCA dem εdem) :
    PKE.ChallengeCCA (scheme kem dem) (q := q) fun D =>
      εkem (absorb (B₁ PK C₁ dem false) D) + εkem (absorb (B₁ PK C₁ dem true) D) +
        εdem (absorb (B₂ M C₂ kem dem) D) + ENNReal.ofReal (2 * δ) := by
  have chain := by
    cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
        (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
      (PKE.ChallengeCCA.Challenge PK M (C₁ × C₂) false • PKE.Real (scheme kem dem) :
          Resource (PKEChallenge PK M (C₁ × C₂) q)) =
          PKE.ChallengeCCA.Game (scheme kem dem) false (budget := q) :=
        (PKE.ChallengeCCA.Game.eq_real (scheme kem dem) false).symm
      _ ≈[ENNReal.ofReal δ] G₁ kem dem false :=
        game_G₁_distance_le kem dem δ correctnessError false
      _ ≃[fun D => εkem (absorb (B₁ PK C₁ dem false) D) + εdem (absorb (B₂ M C₂ kem dem) D) +
          εkem (absorb (B₁ PK C₁ dem true) D)] G₁ kem dem true :=
        G₁_substitutes kem dem εkem εdem kemSecure demSecure
      _ ≈[ENNReal.ofReal δ] PKE.ChallengeCCA.Game (scheme kem dem) true := by
        rw [distance_comm]
        exact game_G₁_distance_le kem dem δ correctnessError true
      _ = PKE.ChallengeCCA.Challenge PK M (C₁ × C₂) true • PKE.Real (scheme kem dem) :=
        PKE.ChallengeCCA.Game.eq_real (scheme kem dem) true
  -- The losses in the order of [1]; `δ ≥ 0` since it bounds a probability.
  have hδ : 0 ≤ δ := le_trans ((Distribution.ProbDist.bind kem.gen fun keys =>
      Distribution.ProbDist.map (fun ck => (keys, ck)) (kem.encaps keys.1)).2.nonNeg.mass_nonneg _)
    correctnessError
  have twice : ENNReal.ofReal (2 * δ) = ENNReal.ofReal δ + ENNReal.ofReal δ := by
    rw [two_mul, ENNReal.ofReal_add hδ hδ]
  exact fun D hD => (chain D hD).trans_eq (by rw [twice]; ring)

/-! ## The CPA variant

The sequence of games of [2, 3]: `Left = R1(E) • KEM-real`, since a KEM + DEM encryption is a KEM
encapsulation and a DEM encryption under its key; `R1(E) • KEM-ideal = R2(K) • OTS-Left`, since
both encrypt `m_L` under a uniform key beside a real encapsulation; and symmetrically for `m_R`
through `R3(E)`. `KEM-ideal` is `KEM.CCA • KEM-real`, which is never asked to decapsulate.

The equalities are maps of the fresh-sampling automata: `R1(E) • KEM-real` is `Left` along the
map of states that keeps the keys; `R1(E) • KEM-ideal` is `R2(K) • OTS-Left` along the map that
keeps the keys and forgets the table of `KEM.CCA`, which has an entry once `OTS-Left` is
initialized. -/

/-! ### Presentations -/

/-- `Left` of a PKE as fresh sampling. -/
noncomputable def PKE.LORCPA.Left.freshSampling {C : Type} [Fintype C]
    (pke : PublicKeyEncryption PK SK M C) (q : PKELeftRight.Port → ℕ) :
    FreshSampling (PKELeftRight.perPort PK M C q) (PKE.LORCPA.Left.perPort pke) :=
  ((FreshSampling.source (PKE.LORCPA.Left.law1 pke) _).parallel
    (FreshSampling.source (PKE.LORCPA.Left.law2 pke) _)).ofProgram none _ _ _

/-- `Right` of a PKE as fresh sampling. -/
noncomputable def PKE.LORCPA.Right.freshSampling {C : Type} [Fintype C]
    (pke : PublicKeyEncryption PK SK M C) (q : PKELeftRight.Port → ℕ) :
    FreshSampling (PKELeftRight.perPort PK M C q) (PKE.LORCPA.Right.perPort pke) :=
  ((FreshSampling.source (PKE.LORCPA.Right.law1 pke) _).parallel
    (FreshSampling.source (PKE.LORCPA.Right.law2 pke) _)).ofProgram none _ _ _

/-- `KEM-real` as fresh sampling. -/
noncomputable def KEM.Real.freshSampling (kem : KEM PK SK C₁ K) (q : Encapsulation.Port → ℕ) :
    FreshSampling (Encapsulation.perPort PK C₁ K q) (KEM.Real.perPort kem) :=
  ((FreshSampling.source (KEM.Real.law1 kem) _).parallel
    (FreshSampling.source (KEM.Real.law2 kem) _)).ofProgram none _ _ _

/-- `KEM.CCA` on a KEM presented as fresh sampling. -/
noncomputable def KEM.CCA.freshSampling {q : Encapsulation.Port → ℕ}
    {R : Resource (Encapsulation.perPort PK C₁ K q)}
    (Φ : FreshSampling (Encapsulation.perPort PK C₁ K q) R) :
    FreshSampling (Encapsulation.perPort PK C₁ K q) (KEM.CCA.perPort PK C₁ K • R) :=
  FreshSampling.ofRightContext _
    ((Φ.parallel (FreshSampling.source (KEM.CCA.law1 PK C₁ K) _)).ofPreservingProgram
      none _ _ _ _ _ _ _)

/-- `R1(E)` on a KEM presented as fresh sampling. -/
noncomputable def R1.freshSampling (dem : SymmetricEncryption K M C₂) (q : PKELeftRight.Port → ℕ)
    {R : Resource (Encapsulation.perPort PK C₁ K (Function.update (kemBudget q) .decaps 0))}
    (Φ : FreshSampling (Encapsulation.perPort PK C₁ K (Function.update (kemBudget q) .decaps 0))
      R) :
    FreshSampling (PKELeftRight.perPort PK M (C₁ × C₂) q) (R1.perLabel PK C₁ dem q • R) :=
  FreshSampling.ofRightContext _
    ((Φ.parallel (FreshSampling.source (R1.law1 PK C₁ dem) (q .enc))).ofLabelBoundedProgram
      (A := PKELeftRight.perPort PK M (C₁ × C₂) q) none (R1.body PK C₁ dem)
      (R1.bound_spec PK C₁ dem) kemCalls (R1.labelBounded dem) q (fun _ hd => hd.2)
      (R1.admits dem q))

/-- `R3(E)` on a KEM presented as fresh sampling. -/
noncomputable def R3.freshSampling (dem : SymmetricEncryption K M C₂) (q : PKELeftRight.Port → ℕ)
    {R : Resource (Encapsulation.perPort PK C₁ K (Function.update (kemBudget q) .decaps 0))}
    (Φ : FreshSampling (Encapsulation.perPort PK C₁ K (Function.update (kemBudget q) .decaps 0))
      R) :
    FreshSampling (PKELeftRight.perPort PK M (C₁ × C₂) q) (R3.perLabel PK C₁ dem q • R) :=
  FreshSampling.ofRightContext _
    ((Φ.parallel (FreshSampling.source (R3.law1 PK C₁ dem) (q .enc))).ofLabelBoundedProgram
      (A := PKELeftRight.perPort PK M (C₁ × C₂) q) none (R3.body PK C₁ dem)
      (R3.bound_spec PK C₁ dem) kemCalls (R3.labelBounded dem) q (fun _ hd => hd.2)
      (R3.admits dem q))

/-- `R2(K)` on a one-time game presented as fresh sampling. -/
noncomputable def 𝓡ₒ.freshSampling (kem : KEM PK SK C₁ K) (q : PKELeftRight.Port → ℕ)
    {R : Resource (LeftRight.perPort M C₂ (𝓡ₒ.insideBudget M C₂ kem q))}
    (Φ : FreshSampling (LeftRight.perPort M C₂ (𝓡ₒ.insideBudget M C₂ kem q)) R) :
    FreshSampling (PKELeftRight.perPort PK M (C₁ × C₂) q) (𝓡ₒ.perPort M C₂ kem • R) :=
  FreshSampling.ofRightContext _
    ((Φ.parallel ((FreshSampling.source (𝓡ₒ.law1 M C₂ kem) _).parallel
      (FreshSampling.source (𝓡ₒ.law2 M C₂ kem) _))).ofPreservingProgram none _ _ _ _ _ _ _)

/-- `OTS-Left` as fresh sampling. -/
noncomputable def Encryption.OTSLeft.freshSampling (dem : SymmetricEncryption K M C₂)
    (q : LeftRight.Port → ℕ) :
    FreshSampling (LeftRight.perPort M C₂ q) (Encryption.OTSLeft.perPort dem) :=
  ((FreshSampling.source (Encryption.OTSLeft.law1 dem) _).parallel
    (FreshSampling.source (Encryption.OTSLeft.law2 dem) _)).ofProgram none _ _ _

/-- `OTS-Right` as fresh sampling. -/
noncomputable def Encryption.OTSRight.freshSampling (dem : SymmetricEncryption K M C₂)
    (q : LeftRight.Port → ℕ) :
    FreshSampling (LeftRight.perPort M C₂ q) (Encryption.OTSRight.perPort dem) :=
  ((FreshSampling.source (Encryption.OTSRight.law1 dem) _).parallel
    (FreshSampling.source (Encryption.OTSRight.law2 dem) _)).ofProgram none _ _ _

/-! ### Steps -/

/-- The fresh-sampling step of `Left`. -/
noncomputable abbrev PKE.LORCPA.Left.freshStep {C : Type} [Fintype C]
    (pke : PublicKeyEncryption PK SK M C) :
    ProbStep (Option (PK × SK) × Unit × Unit) PKELeftRight.Port (PKELeftRight.Input M)
      (PKELeftRight.Output PK C) :=
  (PKE.LORCPA.Left.body pke).probCombine
    (ProbStep.parallel (ProbStep.fresh (PKE.LORCPA.Left.law1 pke))
      (ProbStep.fresh (PKE.LORCPA.Left.law2 pke)))
    (PKE.LORCPA.Left.bound_spec pke)

/-- The fresh-sampling step of `Right`. -/
noncomputable abbrev PKE.LORCPA.Right.freshStep {C : Type} [Fintype C]
    (pke : PublicKeyEncryption PK SK M C) :
    ProbStep (Option (PK × SK) × Unit × Unit) PKELeftRight.Port (PKELeftRight.Input M)
      (PKELeftRight.Output PK C) :=
  (PKE.LORCPA.Right.body pke).probCombine
    (ProbStep.parallel (ProbStep.fresh (PKE.LORCPA.Right.law1 pke))
      (ProbStep.fresh (PKE.LORCPA.Right.law2 pke)))
    (PKE.LORCPA.Right.bound_spec pke)

/-- The fresh-sampling step of `KEM.CCA` on a step of the KEM. -/
noncomputable abbrev KEM.CCA.freshStep {R : Type}
    (stepR :
      ProbStep R Encapsulation.Port (Encapsulation.Input C₁) (Encapsulation.Output PK C₁ K)) :
    ProbStep (Option (List (C₁ × K)) × R × Unit) Encapsulation.Port (Encapsulation.Input C₁)
      (Encapsulation.Output PK C₁ K) :=
  (KEM.CCA.body PK C₁ K).probCombine
    (ProbStep.parallel stepR (ProbStep.fresh (KEM.CCA.law1 PK C₁ K))) (KEM.CCA.bound_spec PK C₁ K)

/-- The fresh-sampling step of `R1(E)` on a step of the KEM. -/
noncomputable abbrev R1.freshStep (dem : SymmetricEncryption K M C₂) {R : Type}
    (stepR :
      ProbStep R Encapsulation.Port (Encapsulation.Input C₁) (Encapsulation.Output PK C₁ K)) :
    ProbStep (Option Unit × R × Unit) PKELeftRight.Port (PKELeftRight.Input M)
      (PKELeftRight.Output PK (C₁ × C₂)) :=
  (R1.body PK C₁ dem).probCombine (ProbStep.parallel stepR (ProbStep.fresh (R1.law1 PK C₁ dem)))
    (R1.bound_spec PK C₁ dem)

/-- The fresh-sampling step of `R3(E)` on a step of the KEM. -/
noncomputable abbrev R3.freshStep (dem : SymmetricEncryption K M C₂) {R : Type}
    (stepR :
      ProbStep R Encapsulation.Port (Encapsulation.Input C₁) (Encapsulation.Output PK C₁ K)) :
    ProbStep (Option Unit × R × Unit) PKELeftRight.Port (PKELeftRight.Input M)
      (PKELeftRight.Output PK (C₁ × C₂)) :=
  (R3.body PK C₁ dem).probCombine (ProbStep.parallel stepR (ProbStep.fresh (R3.law1 PK C₁ dem)))
    (R3.bound_spec PK C₁ dem)

/-- The fresh-sampling step of `R2(K)` on a step of the one-time game. -/
noncomputable abbrev 𝓡ₒ.freshStep (kem : KEM PK SK C₁ K) {R : Type}
    (stepR : ProbStep R LeftRight.Port (LeftRight.Input M) (LeftRight.Output C₂)) :
    ProbStep (Option (PK × SK) × R × Unit × Unit) PKELeftRight.Port (PKELeftRight.Input M)
      (PKELeftRight.Output PK (C₁ × C₂)) :=
  (𝓡ₒ.body M C₂ kem).probCombine
    (ProbStep.parallel stepR (ProbStep.parallel (ProbStep.fresh (𝓡ₒ.law1 M C₂ kem))
      (ProbStep.fresh (𝓡ₒ.law2 M C₂ kem))))
    (𝓡ₒ.bound_spec M C₂ kem)

/-- The fresh-sampling step of `OTS-Left`. -/
noncomputable abbrev Encryption.OTSLeft.freshStep (dem : SymmetricEncryption K M C₂) :
    ProbStep (Option Unit × Unit × Unit) LeftRight.Port (LeftRight.Input M) (LeftRight.Output C₂) :=
  (Encryption.OTSLeft.body dem).probCombine
    (ProbStep.parallel (ProbStep.fresh (Encryption.OTSLeft.law1 dem))
      (ProbStep.fresh (Encryption.OTSLeft.law2 dem)))
    (Encryption.OTSLeft.bound_spec dem)

/-- The fresh-sampling step of `OTS-Right`. -/
noncomputable abbrev Encryption.OTSRight.freshStep (dem : SymmetricEncryption K M C₂) :
    ProbStep (Option Unit × Unit × Unit) LeftRight.Port (LeftRight.Input M) (LeftRight.Output C₂) :=
  (Encryption.OTSRight.body dem).probCombine
    (ProbStep.parallel (ProbStep.fresh (Encryption.OTSRight.law1 dem))
      (ProbStep.fresh (Encryption.OTSRight.law2 dem)))
    (Encryption.OTSRight.bound_spec dem)

/-! ### `Left` and `Right` -/

section LeftRight

omit [DecidableEq SK]

variable {C : Type} [Fintype C]

/-- **`Left` on the public key.** -/
lemma PKE.LORCPA.Left.outcome_publicKey (pke : PublicKeyEncryption PK SK M C) (keys : PK × SK) :
    (PKE.LORCPA.Left.freshStep pke).outcome (some keys, ((), ())) ⟨.publicKey, ()⟩ =
      Finsupp.single ((some keys, ((), ())),
        (⟨.publicKey, keys.1⟩ : Σ o, PKELeftRight.Output PK C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val, Program.probInvoke_inl (a := (some keys, keys.1))
    (by simp [PKE.LORCPA.Left.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **`Left` on an encryption**: `Enc(pk, m_L)`. -/
lemma PKE.LORCPA.Left.outcome_enc (pke : PublicKeyEncryption PK SK M C) (keys : PK × SK)
    (mL mR : M) :
    (PKE.LORCPA.Left.freshStep pke).outcome (some keys, ((), ())) ⟨.enc, (mL, mR)⟩ =
      bindK pke.encryptions.1 fun E => Finsupp.single ((some keys, ((), ())),
        (⟨.enc, E (keys.1, mL)⟩ : Σ o, PKELeftRight.Output PK C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    show PKE.LORCPA.Left.bound pke = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩) (by simp [PKE.LORCPA.Left.body, callProg]),
    ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun E _ => ?_
  rw [Program.probInvoke_inl (a := (some keys, E (keys.1, mL)))
    (by simp [PKE.LORCPA.Left.body, callProg, returnProg, ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`Left` initializes at its first query**: the keys are sampled. -/
lemma PKE.LORCPA.Left.outcome_none (pke : PublicKeyEncryption PK SK M C)
    (x : Σ o, PKELeftRight.Input M o) :
    (PKE.LORCPA.Left.freshStep pke).outcome (none, ((), ())) x =
      bindK pke.gen.1 fun keys =>
        (PKE.LORCPA.Left.freshStep pke).outcome (some keys, ((), ())) x := by
  obtain ⟨o, u⟩ := x
  conv_lhs =>
    rw [ProbStep.outcome, Program.probCombine_val, show PKE.LORCPA.Left.bound pke = 1 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩)
        (by cases o <;> simp [PKE.LORCPA.Left.body, callProg]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun keys _ => ?_
  cases o
  · obtain ⟨⟩ := u
    rw [PKE.LORCPA.Left.outcome_publicKey, Program.probInvoke_inl (a := (some keys, keys.1))
      (by simp [PKE.LORCPA.Left.body, callProg, returnProg, ProbStep.inlReply])]
    simp [fTransform, ProbStep.tagged]
  · obtain ⟨mL, mR⟩ := u
    rw [PKE.LORCPA.Left.outcome_enc, Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
        (by simp [PKE.LORCPA.Left.body, callProg, ProbStep.inlReply]),
      ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
    refine bindK_congr fun E _ => ?_
    rw [Program.probInvoke_inl (a := (some keys, E (keys.1, mL)))
      (by simp [PKE.LORCPA.Left.body, callProg, returnProg, ProbStep.inlReply,
        ProbStep.inrReply])]
    simp [fTransform, ProbStep.tagged]

/-- **`Right` on the public key.** -/
lemma PKE.LORCPA.Right.outcome_publicKey (pke : PublicKeyEncryption PK SK M C) (keys : PK × SK) :
    (PKE.LORCPA.Right.freshStep pke).outcome (some keys, ((), ())) ⟨.publicKey, ()⟩ =
      Finsupp.single ((some keys, ((), ())),
        (⟨.publicKey, keys.1⟩ : Σ o, PKELeftRight.Output PK C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val, Program.probInvoke_inl (a := (some keys, keys.1))
    (by simp [PKE.LORCPA.Right.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **`Right` on an encryption**: `Enc(pk, m_R)`. -/
lemma PKE.LORCPA.Right.outcome_enc (pke : PublicKeyEncryption PK SK M C) (keys : PK × SK)
    (mL mR : M) :
    (PKE.LORCPA.Right.freshStep pke).outcome (some keys, ((), ())) ⟨.enc, (mL, mR)⟩ =
      bindK pke.encryptions.1 fun E => Finsupp.single ((some keys, ((), ())),
        (⟨.enc, E (keys.1, mR)⟩ : Σ o, PKELeftRight.Output PK C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    show PKE.LORCPA.Right.bound pke = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩) (by simp [PKE.LORCPA.Right.body, callProg]),
    ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun E _ => ?_
  rw [Program.probInvoke_inl (a := (some keys, E (keys.1, mR)))
    (by simp [PKE.LORCPA.Right.body, callProg, returnProg, ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`Right` initializes at its first query**: the keys are sampled. -/
lemma PKE.LORCPA.Right.outcome_none (pke : PublicKeyEncryption PK SK M C)
    (x : Σ o, PKELeftRight.Input M o) :
    (PKE.LORCPA.Right.freshStep pke).outcome (none, ((), ())) x =
      bindK pke.gen.1 fun keys =>
        (PKE.LORCPA.Right.freshStep pke).outcome (some keys, ((), ())) x := by
  obtain ⟨o, u⟩ := x
  conv_lhs =>
    rw [ProbStep.outcome, Program.probCombine_val,
      show PKE.LORCPA.Right.bound pke = 1 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩)
        (by cases o <;> simp [PKE.LORCPA.Right.body, callProg]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun keys _ => ?_
  cases o
  · obtain ⟨⟩ := u
    rw [PKE.LORCPA.Right.outcome_publicKey, Program.probInvoke_inl (a := (some keys, keys.1))
      (by simp [PKE.LORCPA.Right.body, callProg, returnProg, ProbStep.inlReply])]
    simp [fTransform, ProbStep.tagged]
  · obtain ⟨mL, mR⟩ := u
    rw [PKE.LORCPA.Right.outcome_enc, Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
        (by simp [PKE.LORCPA.Right.body, callProg, ProbStep.inlReply]),
      ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
    refine bindK_congr fun E _ => ?_
    rw [Program.probInvoke_inl (a := (some keys, E (keys.1, mR)))
      (by simp [PKE.LORCPA.Right.body, callProg, returnProg, ProbStep.inlReply,
        ProbStep.inrReply])]
    simp [fTransform, ProbStep.tagged]

end LeftRight

/-! ### `KEM.CCA` -/

section KEMCCA

omit [DecidableEq PK] [DecidableEq SK] [DecidableEq K]

variable {R : Type}
  (stepR : ProbStep R Encapsulation.Port (Encapsulation.Input C₁) (Encapsulation.Output PK C₁ K))

/-- **`KEM.CCA` reads the KEM first** at the public key and at an encapsulation: on a KEM whose
reply there is a mixture over states, `KEM.CCA` on it is the mixture. -/
lemma KEM.CCA.outcome_bindK (cC : Option (List (C₁ × K))) (r : R) {Z : Type}
    (ρ : Distribution Z) (g : Z → R) (x : Σ i, Encapsulation.Input C₁ i) (hx : x.1 ≠ .decaps)
    (h : stepR.outcome r x = bindK ρ fun z => stepR.outcome (g z) x) :
    (KEM.CCA.freshStep stepR).outcome (cC, (r, ())) x =
      bindK ρ fun z => (KEM.CCA.freshStep stepR).outcome (cC, (g z, ())) x := by
  obtain ⟨o, u⟩ := x
  have h0 : KEM.CCA.body PK C₁ K cC o u [] = .inr ⟨.inl o, u⟩ := by
    cases o <;> cases cC <;> simp_all [KEM.CCA.body, callProg]
  have hb : KEM.CCA.bound PK C₁ K = 1 + 1 := rfl
  conv_lhs => rw [ProbStep.outcome, Program.probCombine_val, hb,
    Program.probInvoke_succ_inr h0, ProbStep.outcome_parallel_inl, h]
  conv_rhs => enter [2, z]; rw [ProbStep.outcome, Program.probCombine_val, hb,
    Program.probInvoke_succ_inr h0, ProbStep.outcome_parallel_inl]
  simp only [fTransform_bindK, bindK_bindK, bindK_fTransform, Function.comp_def]

/-- **`KEM.CCA` on the public key**: the public key of the KEM. -/
lemma KEM.CCA.outcome_publicKey (cC : Option (List (C₁ × K))) (r r' : R) (pk : PK)
    (h : stepR.outcome r ⟨.publicKey, ()⟩ = Finsupp.single (r', ⟨.publicKey, pk⟩) 1) :
    (KEM.CCA.freshStep stepR).outcome (cC, (r, ())) ⟨.publicKey, ()⟩ =
      Finsupp.single ((some (cC.getD []), (r', ())),
        (⟨.publicKey, pk⟩ : Σ i, Encapsulation.Output PK C₁ K i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val, show KEM.CCA.bound PK C₁ K = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl .publicKey, ()⟩)
      (by cases cC <;> simp [KEM.CCA.body, callProg]),
    ProbStep.outcome_parallel_inl, h]
  simp only [fTransform_single, bindK_single, one_smul]
  rw [Program.probInvoke_inl (a := (some (cC.getD []), pk))
    (by cases cC <;> simp [KEM.CCA.body, callProg, returnProg, ProbStep.inlReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`KEM.CCA` on an encapsulation**: the ciphertext `c` of the KEM with a uniform key `k̃`,
and `(c, k̃)` recorded. -/
lemma KEM.CCA.outcome_encaps (cC : Option (List (C₁ × K))) (r : R)
    (ν : Distribution (R × (C₁ × K)))
    (h : stepR.outcome r ⟨.encaps, ()⟩ = bindK ν fun z => Finsupp.single (z.1, ⟨.encaps, z.2⟩) 1) :
    (KEM.CCA.freshStep stepR).outcome (cC, (r, ())) ⟨.encaps, ()⟩ =
      bindK ν fun z => bindK (𝒰[K]).1 fun key =>
        Finsupp.single ((some (cC.getD [] ++ [(z.2.1, key)]), (z.1, ())),
          (⟨.encaps, (z.2.1, key)⟩ : Σ i, Encapsulation.Output PK C₁ K i)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val, show KEM.CCA.bound PK C₁ K = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl .encaps, ()⟩)
      (by cases cC <;> simp [KEM.CCA.body, callProg]),
    ProbStep.outcome_parallel_inl, h]
  simp only [fTransform_bindK, fTransform_single, bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
      (by cases cC <;> simp [KEM.CCA.body, callProg, ProbStep.inlReply]),
    ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun key _ => ?_
  rw [Program.probInvoke_inl (a := (some (cC.getD [] ++ [(z.2.1, key)]), (z.2.1, key)))
    (by cases cC <;> simp [KEM.CCA.body, callProg, returnProg, ProbStep.inlReply,
      ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

end KEMCCA

/-! ### `OTS-Left` and `OTS-Right` -/

section OTS

omit [Fintype PK] [Fintype SK] [Fintype C₁] [DecidableEq PK] [DecidableEq SK] [DecidableEq C₁]
  [DecidableEq C₂]

/-- **`OTS-Left` on an encryption**: `Enc(k, m_L)` for a fresh uniform `k`. -/
lemma Encryption.OTSLeft.outcome_enc (dem : SymmetricEncryption K M C₂) (co : Option Unit)
    (mL mR : M) :
    (Encryption.OTSLeft.freshStep dem).outcome (co, ((), ())) ⟨.enc, (mL, mR)⟩ =
      bindK (𝒰[K]).1 fun k => bindK dem.encryptions.1 fun E =>
        Finsupp.single ((some (), ((), ())),
          (⟨.enc, E (k, mL)⟩ : Σ o, LeftRight.Output C₂ o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    show Encryption.OTSLeft.bound dem = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩)
      (by rcases co with _ | ⟨⟨⟩⟩ <;> simp [Encryption.OTSLeft.body, callProg]),
    ProbStep.outcome_parallel_inl]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun k _ => ?_
  rw [Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
      (by rcases co with _ | ⟨⟨⟩⟩ <;> simp [Encryption.OTSLeft.body, callProg, ProbStep.inlReply]),
    ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun E _ => ?_
  rw [Program.probInvoke_inl (a := (some (), E (k, mL)))
    (by rcases co with _ | ⟨⟨⟩⟩ <;> simp [Encryption.OTSLeft.body, callProg, returnProg,
      ProbStep.inlReply, ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`OTS-Right` on an encryption**: `Enc(k, m_R)` for a fresh uniform `k`. -/
lemma Encryption.OTSRight.outcome_enc (dem : SymmetricEncryption K M C₂) (co : Option Unit)
    (mL mR : M) :
    (Encryption.OTSRight.freshStep dem).outcome (co, ((), ())) ⟨.enc, (mL, mR)⟩ =
      bindK (𝒰[K]).1 fun k => bindK dem.encryptions.1 fun E =>
        Finsupp.single ((some (), ((), ())),
          (⟨.enc, E (k, mR)⟩ : Σ o, LeftRight.Output C₂ o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    show Encryption.OTSRight.bound dem = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩)
      (by rcases co with _ | ⟨⟨⟩⟩ <;> simp [Encryption.OTSRight.body, callProg]),
    ProbStep.outcome_parallel_inl]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun k _ => ?_
  rw [Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
      (by rcases co with _ | ⟨⟨⟩⟩ <;> simp [Encryption.OTSRight.body, callProg, ProbStep.inlReply]),
    ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun E _ => ?_
  rw [Program.probInvoke_inl (a := (some (), E (k, mR)))
    (by rcases co with _ | ⟨⟨⟩⟩ <;> simp [Encryption.OTSRight.body, callProg, returnProg,
      ProbStep.inlReply, ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

end OTS

/-! ### `R1(E)` and `R3(E)` -/

section R1R3

omit [DecidableEq PK] [DecidableEq SK] [DecidableEq C₁] [DecidableEq C₂] [Nonempty K]

variable {R : Type}
  (stepR : ProbStep R Encapsulation.Port (Encapsulation.Input C₁) (Encapsulation.Output PK C₁ K))

/-- **`R1(E)` reads the KEM first**: on a KEM whose replies at the public key and at an
encapsulation are mixtures over states, `R1(E)` on it is the mixture. -/
lemma R1.outcome_bindK (dem : SymmetricEncryption K M C₂) (cR : Option Unit) (r : R)
    {Z : Type} (ρ : Distribution Z) (g : Z → R)
    (hpk : stepR.outcome r ⟨.publicKey, ()⟩ = bindK ρ fun z => stepR.outcome (g z) ⟨.publicKey, ()⟩)
    (henc : stepR.outcome r ⟨.encaps, ()⟩ = bindK ρ fun z => stepR.outcome (g z) ⟨.encaps, ()⟩)
    (x : Σ o, PKELeftRight.Input M o) :
    (R1.freshStep dem stepR).outcome (cR, (r, ())) x =
      bindK ρ fun z => (R1.freshStep dem stepR).outcome (cR, (g z, ())) x := by
  obtain ⟨o, u⟩ := x
  have hb : R1.bound PK C₁ dem = 1 + 1 := rfl
  cases o
  · have h0 : R1.body PK C₁ dem cR .publicKey u [] = .inr ⟨.inl .publicKey, ()⟩ := by
      rcases cR with _ | ⟨⟨⟩⟩ <;> simp [R1.body, callProg]
    conv_lhs => rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0, ProbStep.outcome_parallel_inl, hpk]
    conv_rhs => enter [2, z]; rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0, ProbStep.outcome_parallel_inl]
    simp only [fTransform_bindK, bindK_bindK, bindK_fTransform, Function.comp_def]
  · have h0 : R1.body PK C₁ dem cR .enc u [] = .inr ⟨.inl .encaps, ()⟩ := by
      rcases cR with _ | ⟨⟨⟩⟩ <;> simp [R1.body, callProg]
    conv_lhs => rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0, ProbStep.outcome_parallel_inl, henc]
    conv_rhs => enter [2, z]; rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0, ProbStep.outcome_parallel_inl]
    simp only [fTransform_bindK, bindK_bindK, bindK_fTransform, Function.comp_def]

/-- **`R1(E)` on the public key**: the public key of the KEM. -/
lemma R1.outcome_publicKey (dem : SymmetricEncryption K M C₂) (cR : Option Unit) (r r' : R)
    (pk : PK) (h : stepR.outcome r ⟨.publicKey, ()⟩ = Finsupp.single (r', ⟨.publicKey, pk⟩) 1) :
    (R1.freshStep dem stepR).outcome (cR, (r, ())) ⟨.publicKey, ()⟩ =
      Finsupp.single ((some (), (r', ())),
        (⟨.publicKey, pk⟩ : Σ o, PKELeftRight.Output PK (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val, show R1.bound PK C₁ dem = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl .publicKey, ()⟩)
      (by rcases cR with _ | ⟨⟨⟩⟩ <;> simp [R1.body, callProg]),
    ProbStep.outcome_parallel_inl, h]
  simp only [fTransform_single, bindK_single, one_smul]
  rw [Program.probInvoke_inl (a := (some (), pk))
    (by rcases cR with _ | ⟨⟨⟩⟩ <;> simp [R1.body, callProg, returnProg, ProbStep.inlReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`R1(E)` on an encryption**: `(c_kem, DEM.Enc(k_dem, m_L))` for the encapsulation
`(c_kem, k_dem)` of the KEM. -/
lemma R1.outcome_enc (dem : SymmetricEncryption K M C₂) (cR : Option Unit) (r : R)
    (ν : Distribution (R × (C₁ × K)))
    (h : stepR.outcome r ⟨.encaps, ()⟩ = bindK ν fun z => Finsupp.single (z.1, ⟨.encaps, z.2⟩) 1)
    (mL mR : M) :
    (R1.freshStep dem stepR).outcome (cR, (r, ())) ⟨.enc, (mL, mR)⟩ =
      bindK ν fun z => bindK dem.encryptions.1 fun E =>
        Finsupp.single ((some (), (z.1, ())),
          (⟨.enc, (z.2.1, E (z.2.2, mL))⟩ : Σ o, PKELeftRight.Output PK (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val, show R1.bound PK C₁ dem = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl .encaps, ()⟩)
      (by rcases cR with _ | ⟨⟨⟩⟩ <;> simp [R1.body, callProg]),
    ProbStep.outcome_parallel_inl, h]
  simp only [fTransform_bindK, fTransform_single, bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
      (by rcases cR with _ | ⟨⟨⟩⟩ <;> simp [R1.body, callProg, ProbStep.inlReply]),
    ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun E _ => ?_
  rw [Program.probInvoke_inl (a := (some (), (z.2.1, E (z.2.2, mL))))
    (by rcases cR with _ | ⟨⟨⟩⟩ <;> simp [R1.body, callProg, returnProg, ProbStep.inlReply,
      ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`R3(E)` reads the KEM first**: on a KEM whose replies at the public key and at an
encapsulation are mixtures over states, `R3(E)` on it is the mixture. -/
lemma R3.outcome_bindK (dem : SymmetricEncryption K M C₂) (cR : Option Unit) (r : R)
    {Z : Type} (ρ : Distribution Z) (g : Z → R)
    (hpk : stepR.outcome r ⟨.publicKey, ()⟩ = bindK ρ fun z => stepR.outcome (g z) ⟨.publicKey, ()⟩)
    (henc : stepR.outcome r ⟨.encaps, ()⟩ = bindK ρ fun z => stepR.outcome (g z) ⟨.encaps, ()⟩)
    (x : Σ o, PKELeftRight.Input M o) :
    (R3.freshStep dem stepR).outcome (cR, (r, ())) x =
      bindK ρ fun z => (R3.freshStep dem stepR).outcome (cR, (g z, ())) x := by
  obtain ⟨o, u⟩ := x
  have hb : R3.bound PK C₁ dem = 1 + 1 := rfl
  cases o
  · have h0 : R3.body PK C₁ dem cR .publicKey u [] = .inr ⟨.inl .publicKey, ()⟩ := by
      rcases cR with _ | ⟨⟨⟩⟩ <;> simp [R3.body, callProg]
    conv_lhs => rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0, ProbStep.outcome_parallel_inl, hpk]
    conv_rhs => enter [2, z]; rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0, ProbStep.outcome_parallel_inl]
    simp only [fTransform_bindK, bindK_bindK, bindK_fTransform, Function.comp_def]
  · have h0 : R3.body PK C₁ dem cR .enc u [] = .inr ⟨.inl .encaps, ()⟩ := by
      rcases cR with _ | ⟨⟨⟩⟩ <;> simp [R3.body, callProg]
    conv_lhs => rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0, ProbStep.outcome_parallel_inl, henc]
    conv_rhs => enter [2, z]; rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0, ProbStep.outcome_parallel_inl]
    simp only [fTransform_bindK, bindK_bindK, bindK_fTransform, Function.comp_def]

/-- **`R3(E)` on the public key**: the public key of the KEM. -/
lemma R3.outcome_publicKey (dem : SymmetricEncryption K M C₂) (cR : Option Unit) (r r' : R)
    (pk : PK) (h : stepR.outcome r ⟨.publicKey, ()⟩ = Finsupp.single (r', ⟨.publicKey, pk⟩) 1) :
    (R3.freshStep dem stepR).outcome (cR, (r, ())) ⟨.publicKey, ()⟩ =
      Finsupp.single ((some (), (r', ())),
        (⟨.publicKey, pk⟩ : Σ o, PKELeftRight.Output PK (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val, show R3.bound PK C₁ dem = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl .publicKey, ()⟩)
      (by rcases cR with _ | ⟨⟨⟩⟩ <;> simp [R3.body, callProg]),
    ProbStep.outcome_parallel_inl, h]
  simp only [fTransform_single, bindK_single, one_smul]
  rw [Program.probInvoke_inl (a := (some (), pk))
    (by rcases cR with _ | ⟨⟨⟩⟩ <;> simp [R3.body, callProg, returnProg, ProbStep.inlReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`R3(E)` on an encryption**: `(c_kem, DEM.Enc(k_dem, m_R))` for the encapsulation
`(c_kem, k_dem)` of the KEM. -/
lemma R3.outcome_enc (dem : SymmetricEncryption K M C₂) (cR : Option Unit) (r : R)
    (ν : Distribution (R × (C₁ × K)))
    (h : stepR.outcome r ⟨.encaps, ()⟩ = bindK ν fun z => Finsupp.single (z.1, ⟨.encaps, z.2⟩) 1)
    (mL mR : M) :
    (R3.freshStep dem stepR).outcome (cR, (r, ())) ⟨.enc, (mL, mR)⟩ =
      bindK ν fun z => bindK dem.encryptions.1 fun E =>
        Finsupp.single ((some (), (z.1, ())),
          (⟨.enc, (z.2.1, E (z.2.2, mR))⟩ : Σ o, PKELeftRight.Output PK (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val, show R3.bound PK C₁ dem = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl .encaps, ()⟩)
      (by rcases cR with _ | ⟨⟨⟩⟩ <;> simp [R3.body, callProg]),
    ProbStep.outcome_parallel_inl, h]
  simp only [fTransform_bindK, fTransform_single, bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
      (by rcases cR with _ | ⟨⟨⟩⟩ <;> simp [R3.body, callProg, ProbStep.inlReply]),
    ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun E _ => ?_
  rw [Program.probInvoke_inl (a := (some (), (z.2.1, E (z.2.2, mR))))
    (by rcases cR with _ | ⟨⟨⟩⟩ <;> simp [R3.body, callProg, returnProg, ProbStep.inlReply,
      ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

end R1R3

/-! ### `R2(K)` -/

section R2

omit [DecidableEq SK] [DecidableEq C₁] [DecidableEq K] [DecidableEq M] [DecidableEq C₂]
  [Nonempty K]

variable {R : Type} (stepR : ProbStep R LeftRight.Port (LeftRight.Input M) (LeftRight.Output C₂))

/-- **`R2(K)` on the public key.** -/
lemma 𝓡ₒ.outcome_publicKey (kem : KEM PK SK C₁ K) (keys : PK × SK) (r : R) :
    (𝓡ₒ.freshStep kem stepR).outcome (some keys, (r, ((), ()))) ⟨.publicKey, ()⟩ =
      Finsupp.single ((some keys, (r, ((), ()))),
        (⟨.publicKey, keys.1⟩ : Σ o, PKELeftRight.Output PK (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some keys, keys.1)) (by simp [𝓡ₒ.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **`R2(K)` on an encryption**: `(c_kem, c_dem)` for `(c_kem, _) ← KEM.Enc(pk)` and the
encryption `c_dem` of the one-time game. -/
lemma 𝓡ₒ.outcome_enc (kem : KEM PK SK C₁ K) (keys : PK × SK) (r : R) (mL mR : M)
    (ν : Distribution (R × C₂))
    (h : stepR.outcome r ⟨.enc, (mL, mR)⟩ = bindK ν fun z => Finsupp.single (z.1, ⟨.enc, z.2⟩) 1) :
    (𝓡ₒ.freshStep kem stepR).outcome (some keys, (r, ((), ()))) ⟨.enc, (mL, mR)⟩ =
      bindK kem.encapsulations.1 fun e => bindK ν fun z =>
        Finsupp.single ((some keys, (z.1, ((), ()))),
          (⟨.enc, ((e keys.1).1, z.2)⟩ : Σ o, PKELeftRight.Output PK (C₁ × C₂) o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val, show 𝓡ₒ.bound M C₂ kem = 2 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inr (.inr ()), ()⟩) (by simp [𝓡ₒ.body, callProg]),
    ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun e _ => ?_
  rw [Program.probInvoke_succ_inr (q := ⟨.inl .enc, (mL, mR)⟩)
      (by simp [𝓡ₒ.body, callProg, ProbStep.inrReply]),
    ProbStep.outcome_parallel_inl, h]
  simp only [fTransform_bindK, fTransform_single, bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_inl (a := (some keys, ((e keys.1).1, z.2)))
    (by simp [𝓡ₒ.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

/-- **`R2(K)` initializes at its first query**: the keys are sampled. -/
lemma 𝓡ₒ.outcome_none (kem : KEM PK SK C₁ K) (r : R) (x : Σ o, PKELeftRight.Input M o) :
    (𝓡ₒ.freshStep kem stepR).outcome (none, (r, ((), ()))) x =
      bindK kem.gen.1 fun keys =>
        (𝓡ₒ.freshStep kem stepR).outcome (some keys, (r, ((), ()))) x := by
  obtain ⟨o, u⟩ := x
  conv_lhs =>
    rw [ProbStep.outcome, Program.probCombine_val, show 𝓡ₒ.bound M C₂ kem = 2 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inr (.inl ()), ()⟩)
        (by cases o <;> simp [𝓡ₒ.body, callProg]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun keys _ => ?_
  cases o
  · obtain ⟨⟩ := u
    rw [𝓡ₒ.outcome_publicKey, Program.probInvoke_inl (a := (some keys, keys.1))
      (by simp [𝓡ₒ.body, callProg, returnProg, ProbStep.inrReply, ProbStep.inlReply])]
    simp [fTransform, ProbStep.tagged]
  · -- The encapsulations and the one-time game answer as after the keys.
    obtain ⟨mL, mR⟩ := u
    conv_rhs => rw [ProbStep.outcome, Program.probCombine_val,
      show 𝓡ₒ.bound M C₂ kem = 2 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inr (.inr ()), ()⟩) (by simp [𝓡ₒ.body, callProg]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr]
    conv_lhs => rw [Program.probInvoke_succ_inr (q := ⟨.inr (.inr ()), ()⟩)
      (by simp [𝓡ₒ.body, callProg, ProbStep.inrReply, ProbStep.inlReply]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform,
      fTransform_fTransform, Function.comp_def, fTransform_bindK, ProbStep.tagged]
    refine bindK_congr fun e _ => ?_
    conv_rhs => rw [Program.probInvoke_succ_inr (q := ⟨.inl .enc, (mL, mR)⟩)
      (by simp [𝓡ₒ.body, callProg, ProbStep.inrReply]), ProbStep.outcome_parallel_inl]
    conv_lhs => rw [Program.probInvoke_succ_inr (q := ⟨.inl .enc, (mL, mR)⟩)
      (by simp [𝓡ₒ.body, callProg, ProbStep.inrReply, ProbStep.inlReply]),
      ProbStep.outcome_parallel_inl]
    simp only [bindK_fTransform, fTransform_bindK]
    refine bindK_congr fun p hp => ?_
    obtain ⟨y', hy⟩ := Program.mem_support_outcome hp
    obtain ⟨r', p2⟩ := p
    dsimp only at hy
    subst hy
    dsimp only [Function.comp_apply]
    rw [Program.probInvoke_inl (a := (some keys, ((e keys.1).1, y')))
        (by simp [𝓡ₒ.body, callProg, returnProg, ProbStep.inrReply, ProbStep.inlReply]),
      Program.probInvoke_inl (a := (some keys, ((e keys.1).1, y')))
        (by simp [𝓡ₒ.body, callProg, returnProg, ProbStep.inrReply, ProbStep.inlReply])]

end R2

/-! ### The libraries as converters on the real systems -/

section LibrarySteps

omit [DecidableEq C₂] [Nonempty K]

variable {C : Type} [Fintype C]

/-- `Left` on the public key and `E_pk` as fresh sampling. -/
noncomputable def PKE.Left.freshSamplingReal (pke : PublicKeyEncryption PK SK M C)
    (q : PKELeftRight.Port → ℕ) :
    FreshSampling (PKELeftRight.perPort PK M C q)
      (PKE.Left.perLabel PK M C q • PKE.Real.perPort pke) :=
  (((FreshSampling.source (PKE.Real.law1 pke) _).parallel
    (FreshSampling.source (PKE.Real.law2 pke) _)).ofProgram none _ _ _ :
      FreshSampling (PKE.perPort PK M C (PKE.LORCPA.insideBudget q))
        (PKE.Real.perPort pke)).ofLabelBoundedProgram (A := PKELeftRight.perPort PK M C q) none
    (PKE.Left.body PK M C) (PKE.Left.bound_spec PK M C) PKE.LORCPA.insideCalls
    PKE.Left.labelBounded q (fun _ hd => hd.2) (PKE.LORCPA.admits q)

/-- `Right` on the public key and `E_pk` as fresh sampling. -/
noncomputable def PKE.Right.freshSamplingReal (pke : PublicKeyEncryption PK SK M C)
    (q : PKELeftRight.Port → ℕ) :
    FreshSampling (PKELeftRight.perPort PK M C q)
      (PKE.Right.perLabel PK M C q • PKE.Real.perPort pke) :=
  (((FreshSampling.source (PKE.Real.law1 pke) _).parallel
    (FreshSampling.source (PKE.Real.law2 pke) _)).ofProgram none _ _ _ :
      FreshSampling (PKE.perPort PK M C (PKE.LORCPA.insideBudget q))
        (PKE.Real.perPort pke)).ofLabelBoundedProgram (A := PKELeftRight.perPort PK M C q) none
    (PKE.Right.body PK M C) (PKE.Right.bound_spec PK M C) PKE.LORCPA.insideCalls
    PKE.Right.labelBounded q (fun _ hd => hd.2) (PKE.LORCPA.admits q)

/-- `Left` of Commons on the one-time encryption system as fresh sampling. -/
noncomputable def Encryption.Left.freshSamplingOneTime (dem : SymmetricEncryption K M C₂)
    (q : LeftRight.Port → ℕ) :
    FreshSampling (LeftRight.perPort M C₂ q)
      (Encryption.Left.perPort M C₂ • Encryption.OneTime.perPort dem) := by
  unfold Encryption.Left.perPort Encryption.Left.perPortProgram
  exact (((FreshSampling.source (Encryption.OneTime.law1 dem) _).parallel
    (FreshSampling.source (Encryption.OneTime.law2 dem) _)).ofProgram none _ _ _ :
      FreshSampling (Encryption.perPort M C₂ (Encryption.Left.insideBudget M C₂ q))
        (Encryption.OneTime.perPort dem)).ofPreservingProgram none _ _ _ _ _ _ _

/-- `Right` of Commons on the one-time encryption system as fresh sampling. -/
noncomputable def Encryption.Right.freshSamplingOneTime (dem : SymmetricEncryption K M C₂)
    (q : LeftRight.Port → ℕ) :
    FreshSampling (LeftRight.perPort M C₂ q)
      (Encryption.Right.perPort M C₂ • Encryption.OneTime.perPort dem) := by
  unfold Encryption.Right.perPort Encryption.Right.perPortProgram
  exact (((FreshSampling.source (Encryption.OneTime.law1 dem) _).parallel
    (FreshSampling.source (Encryption.OneTime.law2 dem) _)).ofProgram none _ _ _ :
      FreshSampling (Encryption.perPort M C₂ (Encryption.Right.insideBudget M C₂ q))
        (Encryption.OneTime.perPort dem)).ofPreservingProgram none _ _ _ _ _ _ _

/-- The fresh-sampling step of the one-time encryption system. -/
noncomputable abbrev Encryption.OneTime.freshStep (dem : SymmetricEncryption K M C₂) :
    ProbStep (Option Unit × Unit × Unit) Encryption.Port (Encryption.Input M)
      (Encryption.Output C₂) :=
  (Encryption.OneTime.body dem).probCombine
    (ProbStep.parallel (ProbStep.fresh (Encryption.OneTime.law1 dem))
      (ProbStep.fresh (Encryption.OneTime.law2 dem)))
    (Encryption.OneTime.bound_spec dem)

/-- **The one-time encryption system on an encryption**: `Enc(k, m)` for a fresh `k ← Gen`. -/
lemma Encryption.OneTime.outcome_enc (dem : SymmetricEncryption K M C₂) (co : Option Unit)
    (m : M) :
    (Encryption.OneTime.freshStep dem).outcome (co, ((), ())) ⟨.enc, m⟩ =
      bindK dem.gen.1 fun k => bindK dem.encryptions.1 fun E =>
        Finsupp.single ((some (), ((), ())),
          (⟨.enc, E (k, m)⟩ : Σ o, Encryption.Output C₂ o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    show Encryption.OneTime.bound dem = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩)
      (by rcases co with _ | ⟨⟨⟩⟩ <;> simp [Encryption.OneTime.body, callProg]),
    ProbStep.outcome_parallel_inl]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun k _ => ?_
  rw [Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
      (by rcases co with _ | ⟨⟨⟩⟩ <;> simp [Encryption.OneTime.body, callProg, ProbStep.inlReply]),
    ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
    Function.comp_def, fTransform_bindK, ProbStep.tagged]
  refine bindK_congr fun E _ => ?_
  rw [Program.probInvoke_inl (a := (some (), E (k, m)))
    (by rcases co with _ | ⟨⟨⟩⟩ <;> simp [Encryption.OneTime.body, callProg, returnProg,
      ProbStep.inlReply, ProbStep.inrReply])]
  simp [fTransform, ProbStep.tagged]

omit [DecidableEq M] in
/-- **`Left` of Commons on an encryption**: the encryption of `m_L` by the inside system. -/
lemma Encryption.Left.outcome_enc {R : Type}
    (stepR : ProbStep R Encryption.Port (Encryption.Input M) (Encryption.Output C₂))
    (cL : Option Unit) (r : R) (mL mR : M) (ν : Distribution (R × C₂))
    (h : stepR.outcome r ⟨.enc, mL⟩ = bindK ν fun z => Finsupp.single (z.1, ⟨.enc, z.2⟩) 1) :
    ((Encryption.Left.body M C₂).probCombine stepR (Encryption.Left.bound_spec M C₂)).outcome
        (cL, r) ⟨.enc, (mL, mR)⟩ =
      bindK ν fun z => Finsupp.single ((some (), z.1),
        (⟨.enc, z.2⟩ : Σ o, LeftRight.Output C₂ o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val, show Encryption.Left.bound M C₂ = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.enc, mL⟩)
      (by rcases cL with _ | ⟨⟨⟩⟩ <;> simp [Encryption.Left.body, callProg]), h]
  simp only [fTransform_bindK, bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_inl (a := (some (), z.2))
    (by rcases cL with _ | ⟨⟨⟩⟩ <;> simp [Encryption.Left.body, callProg, returnProg])]
  simp [fTransform, ProbStep.tagged]

omit [DecidableEq M] in
/-- **`Right` of Commons on an encryption**: the encryption of `m_R` by the inside system. -/
lemma Encryption.Right.outcome_enc {R : Type}
    (stepR : ProbStep R Encryption.Port (Encryption.Input M) (Encryption.Output C₂))
    (cL : Option Unit) (r : R) (mL mR : M) (ν : Distribution (R × C₂))
    (h : stepR.outcome r ⟨.enc, mR⟩ = bindK ν fun z => Finsupp.single (z.1, ⟨.enc, z.2⟩) 1) :
    ((Encryption.Right.body M C₂).probCombine stepR (Encryption.Right.bound_spec M C₂)).outcome
        (cL, r) ⟨.enc, (mL, mR)⟩ =
      bindK ν fun z => Finsupp.single ((some (), z.1),
        (⟨.enc, z.2⟩ : Σ o, LeftRight.Output C₂ o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    show Encryption.Right.bound M C₂ = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.enc, mR⟩)
      (by rcases cL with _ | ⟨⟨⟩⟩ <;> simp [Encryption.Right.body, callProg]), h]
  simp only [fTransform_bindK, bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_inl (a := (some (), z.2))
    (by rcases cL with _ | ⟨⟨⟩⟩ <;> simp [Encryption.Right.body, callProg, returnProg])]
  simp [fTransform, ProbStep.tagged]

variable {R : Type} (stepR : ProbStep R PKE.Port (PKE.Input M C) (PKE.Output PK M C))

omit [DecidableEq PK] [DecidableEq M] in
/-- **`Left` reads the PKE first**: on a PKE whose replies are mixtures over states, `Left` on
it is the mixture. -/
lemma PKE.Left.outcome_bindK (cL : Option Unit) (r : R) {Z : Type} (ρ : Distribution Z)
    (g : Z → R) (h : ∀ x, stepR.outcome r x = bindK ρ fun z => stepR.outcome (g z) x)
    (x : Σ o, PKELeftRight.Input M o) :
    ((PKE.Left.body PK M C).probCombine stepR (PKE.Left.bound_spec PK M C)).outcome (cL, r) x =
      bindK ρ fun z =>
        ((PKE.Left.body PK M C).probCombine stepR (PKE.Left.bound_spec PK M C)).outcome
          (cL, g z) x := by
  obtain ⟨o, u⟩ := x
  have hb : PKE.Left.bound PK M C = 0 + 1 := rfl
  cases o
  · have h0 : PKE.Left.body PK M C cL .publicKey u [] = .inr ⟨.publicKey, ()⟩ := by
      rcases cL with _ | ⟨⟨⟩⟩ <;> simp [PKE.Left.body, callProg]
    conv_lhs => rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0, h]
    conv_rhs => enter [2, z]; rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0]
    simp only [fTransform_bindK, bindK_bindK]
  · have h0 : PKE.Left.body PK M C cL .enc u [] = .inr ⟨.enc, u.1⟩ := by
      rcases cL with _ | ⟨⟨⟩⟩ <;> simp [PKE.Left.body, callProg]
    conv_lhs => rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0, h]
    conv_rhs => enter [2, z]; rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0]
    simp only [fTransform_bindK, bindK_bindK]

omit [DecidableEq PK] [DecidableEq M] in
/-- **`Right` reads the PKE first**: on a PKE whose replies are mixtures over states, `Right` on
it is the mixture. -/
lemma PKE.Right.outcome_bindK (cL : Option Unit) (r : R) {Z : Type} (ρ : Distribution Z)
    (g : Z → R) (h : ∀ x, stepR.outcome r x = bindK ρ fun z => stepR.outcome (g z) x)
    (x : Σ o, PKELeftRight.Input M o) :
    ((PKE.Right.body PK M C).probCombine stepR (PKE.Right.bound_spec PK M C)).outcome (cL, r) x =
      bindK ρ fun z =>
        ((PKE.Right.body PK M C).probCombine stepR (PKE.Right.bound_spec PK M C)).outcome
          (cL, g z) x := by
  obtain ⟨o, u⟩ := x
  have hb : PKE.Right.bound PK M C = 0 + 1 := rfl
  cases o
  · have h0 : PKE.Right.body PK M C cL .publicKey u [] = .inr ⟨.publicKey, ()⟩ := by
      rcases cL with _ | ⟨⟨⟩⟩ <;> simp [PKE.Right.body, callProg]
    conv_lhs => rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0, h]
    conv_rhs => enter [2, z]; rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0]
    simp only [fTransform_bindK, bindK_bindK]
  · have h0 : PKE.Right.body PK M C cL .enc u [] = .inr ⟨.enc, u.2⟩ := by
      rcases cL with _ | ⟨⟨⟩⟩ <;> simp [PKE.Right.body, callProg]
    conv_lhs => rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0, h]
    conv_rhs => enter [2, z]; rw [ProbStep.outcome, Program.probCombine_val, hb,
      Program.probInvoke_succ_inr h0]
    simp only [fTransform_bindK, bindK_bindK]

omit [DecidableEq PK] [DecidableEq M] in
/-- **`Left` and `Right` on the public key**: the public key of the PKE. -/
lemma PKE.Left.outcome_publicKey (cL : Option Unit) (r : R) (ν : Distribution (R × PK))
    (h : stepR.outcome r ⟨.publicKey, ()⟩ =
      bindK ν fun z => Finsupp.single (z.1, ⟨.publicKey, z.2⟩) 1) :
    ((PKE.Left.body PK M C).probCombine stepR (PKE.Left.bound_spec PK M C)).outcome (cL, r)
        ⟨.publicKey, ()⟩ =
      bindK ν fun z => Finsupp.single ((some (), z.1),
        (⟨.publicKey, z.2⟩ : Σ o, PKELeftRight.Output PK C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val, show PKE.Left.bound PK M C = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.publicKey, ()⟩)
      (by rcases cL with _ | ⟨⟨⟩⟩ <;> simp [PKE.Left.body, callProg]), h]
  simp only [fTransform_bindK, bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_inl (a := (some (), z.2))
    (by rcases cL with _ | ⟨⟨⟩⟩ <;> simp [PKE.Left.body, callProg, returnProg])]
  simp [fTransform, ProbStep.tagged]

omit [DecidableEq PK] [DecidableEq M] in
/-- **`Right` on the public key**: the public key of the PKE. -/
lemma PKE.Right.outcome_publicKey (cL : Option Unit) (r : R) (ν : Distribution (R × PK))
    (h : stepR.outcome r ⟨.publicKey, ()⟩ =
      bindK ν fun z => Finsupp.single (z.1, ⟨.publicKey, z.2⟩) 1) :
    ((PKE.Right.body PK M C).probCombine stepR (PKE.Right.bound_spec PK M C)).outcome (cL, r)
        ⟨.publicKey, ()⟩ =
      bindK ν fun z => Finsupp.single ((some (), z.1),
        (⟨.publicKey, z.2⟩ : Σ o, PKELeftRight.Output PK C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val, show PKE.Right.bound PK M C = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.publicKey, ()⟩)
      (by rcases cL with _ | ⟨⟨⟩⟩ <;> simp [PKE.Right.body, callProg]), h]
  simp only [fTransform_bindK, bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_inl (a := (some (), z.2))
    (by rcases cL with _ | ⟨⟨⟩⟩ <;> simp [PKE.Right.body, callProg, returnProg])]
  simp [fTransform, ProbStep.tagged]

omit [DecidableEq PK] [DecidableEq M] in
/-- **`Left` on an encryption**: the encryption of `m_L` by the PKE. -/
lemma PKE.Left.outcome_enc (cL : Option Unit) (r : R) (mL mR : M) (ν : Distribution (R × C))
    (h : stepR.outcome r ⟨.enc, mL⟩ = bindK ν fun z => Finsupp.single (z.1, ⟨.enc, z.2⟩) 1) :
    ((PKE.Left.body PK M C).probCombine stepR (PKE.Left.bound_spec PK M C)).outcome (cL, r)
        ⟨.enc, (mL, mR)⟩ =
      bindK ν fun z => Finsupp.single ((some (), z.1),
        (⟨.enc, z.2⟩ : Σ o, PKELeftRight.Output PK C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val, show PKE.Left.bound PK M C = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.enc, mL⟩)
      (by rcases cL with _ | ⟨⟨⟩⟩ <;> simp [PKE.Left.body, callProg]), h]
  simp only [fTransform_bindK, bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_inl (a := (some (), z.2))
    (by rcases cL with _ | ⟨⟨⟩⟩ <;> simp [PKE.Left.body, callProg, returnProg])]
  simp [fTransform, ProbStep.tagged]

omit [DecidableEq PK] [DecidableEq M] in
/-- **`Right` on an encryption**: the encryption of `m_R` by the PKE. -/
lemma PKE.Right.outcome_enc (cL : Option Unit) (r : R) (mL mR : M) (ν : Distribution (R × C))
    (h : stepR.outcome r ⟨.enc, mR⟩ = bindK ν fun z => Finsupp.single (z.1, ⟨.enc, z.2⟩) 1) :
    ((PKE.Right.body PK M C).probCombine stepR (PKE.Right.bound_spec PK M C)).outcome (cL, r)
        ⟨.enc, (mL, mR)⟩ =
      bindK ν fun z => Finsupp.single ((some (), z.1),
        (⟨.enc, z.2⟩ : Σ o, PKELeftRight.Output PK C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val, show PKE.Right.bound PK M C = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.enc, mR⟩)
      (by rcases cL with _ | ⟨⟨⟩⟩ <;> simp [PKE.Right.body, callProg]), h]
  simp only [fTransform_bindK, bindK_bindK, bindK_single, one_smul]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_inl (a := (some (), z.2))
    (by rcases cL with _ | ⟨⟨⟩⟩ <;> simp [PKE.Right.body, callProg, returnProg])]
  simp [fTransform, ProbStep.tagged]

end LibrarySteps

section Presentations

omit [DecidableEq SK] in
/-- **`Left` is `Left` on the public key and `E_pk`.** -/
lemma PKE.LORCPA.Left.eq_real {C : Type} [Fintype C] (pke : PublicKeyEncryption PK SK M C)
    (q : PKELeftRight.Port → ℕ) :
    (PKE.LORCPA.Left.perPort pke : Resource (PKELeftRight.perPort PK M C q)) =
      PKE.Left.perLabel PK M C q • PKE.Real.perPort pke := by
  -- Once the PKE has its keys, `Left` on it steps as `Left` of `CPA`.
  have hsome : ∀ (cL : Option Unit) (keys : PK × SK) (x : Σ o, PKELeftRight.Input M o),
      ((PKE.Left.body PK M C).probCombine (PKE.Real.freshStep pke)
          (PKE.Left.bound_spec PK M C)).outcome (cL, (some keys, ((), ()))) x =
        fTransform (Prod.map (fun s => (s.1.map fun _ => (), (s.1, ((), ())))) id)
          ((PKE.LORCPA.Left.freshStep pke).outcome (some keys, ((), ())) x) := by
    rintro cL keys ⟨_ | _, u⟩
    · obtain ⟨⟩ := u
      rw [PKE.Left.outcome_publicKey _ cL _ (Finsupp.single ((some keys, ((), ())), keys.1) 1)
          (by rw [PKE.Real.outcome_publicKey, bindK_single, one_smul]),
        bindK_single, one_smul, PKE.LORCPA.Left.outcome_publicKey, fTransform_single]
      rfl
    · obtain ⟨mL, mR⟩ := u
      rw [PKE.Left.outcome_enc _ cL _ mL mR (bindK pke.encryptions.1 fun E =>
          Finsupp.single ((some keys, ((), ())), E (keys.1, mL)) 1)
          (by
            rw [PKE.Real.outcome_enc, bindK_bindK]
            exact bindK_congr fun E _ => by rw [bindK_single, one_smul]),
        PKE.LORCPA.Left.outcome_enc, fTransform_bindK, bindK_bindK]
      refine bindK_congr fun E _ => ?_
      rw [bindK_single, one_smul, fTransform_single]
      rfl
  refine (PKE.LORCPA.Left.freshSampling pke q).eq_fresh.trans
    (Eq.trans ?_ (PKE.Left.freshSamplingReal pke q).eq_fresh.symm)
  refine Resource.ofProbAutomaton_eq_of_map _ _ _ _
    (fun s => (s.1.map fun _ => (), (s.1, ((), ())))) ?_ ?_ <;>
    dsimp only [PKE.LORCPA.Left.freshSampling, PKE.Left.freshSamplingReal,
      FreshSampling.ofLabelBoundedProgram, FreshSampling.ofProgram, FreshSampling.parallel,
      FreshSampling.source, Distribution.ProbDist.single]
  · rintro ⟨_ | keys, ⟨⟩, ⟨⟩⟩ x
    · -- Both sample the keys at the first query.
      refine (PKE.Left.outcome_bindK (PKE.Real.freshStep pke) none (none, ((), ())) pke.gen.1
        (fun keys => (some keys, ((), ()))) (PKE.Real.outcome_none pke) x).trans ?_
      rw [PKE.LORCPA.Left.outcome_none, fTransform_bindK]
      exact bindK_congr fun keys _ => hsome none keys x
    · exact hsome (some ()) keys x
  · rw [fTransform_single]
    rfl

omit [DecidableEq SK] in
/-- **`Right` is `Right` on the public key and `E_pk`.** -/
lemma PKE.LORCPA.Right.eq_real {C : Type} [Fintype C] (pke : PublicKeyEncryption PK SK M C)
    (q : PKELeftRight.Port → ℕ) :
    (PKE.LORCPA.Right.perPort pke : Resource (PKELeftRight.perPort PK M C q)) =
      PKE.Right.perLabel PK M C q • PKE.Real.perPort pke := by
  -- Once the PKE has its keys, `Right` on it steps as `Right` of `CPA`.
  have hsome : ∀ (cL : Option Unit) (keys : PK × SK) (x : Σ o, PKELeftRight.Input M o),
      ((PKE.Right.body PK M C).probCombine (PKE.Real.freshStep pke)
          (PKE.Right.bound_spec PK M C)).outcome (cL, (some keys, ((), ()))) x =
        fTransform (Prod.map (fun s => (s.1.map fun _ => (), (s.1, ((), ())))) id)
          ((PKE.LORCPA.Right.freshStep pke).outcome (some keys, ((), ())) x) := by
    rintro cL keys ⟨_ | _, u⟩
    · obtain ⟨⟩ := u
      rw [PKE.Right.outcome_publicKey _ cL _ (Finsupp.single ((some keys, ((), ())), keys.1) 1)
          (by rw [PKE.Real.outcome_publicKey, bindK_single, one_smul]),
        bindK_single, one_smul, PKE.LORCPA.Right.outcome_publicKey, fTransform_single]
      rfl
    · obtain ⟨mL, mR⟩ := u
      rw [PKE.Right.outcome_enc _ cL _ mL mR (bindK pke.encryptions.1 fun E =>
          Finsupp.single ((some keys, ((), ())), E (keys.1, mR)) 1)
          (by
            rw [PKE.Real.outcome_enc, bindK_bindK]
            exact bindK_congr fun E _ => by rw [bindK_single, one_smul]),
        PKE.LORCPA.Right.outcome_enc, fTransform_bindK, bindK_bindK]
      refine bindK_congr fun E _ => ?_
      rw [bindK_single, one_smul, fTransform_single]
      rfl
  refine (PKE.LORCPA.Right.freshSampling pke q).eq_fresh.trans
    (Eq.trans ?_ (PKE.Right.freshSamplingReal pke q).eq_fresh.symm)
  refine Resource.ofProbAutomaton_eq_of_map _ _ _ _
    (fun s => (s.1.map fun _ => (), (s.1, ((), ())))) ?_ ?_ <;>
    dsimp only [PKE.LORCPA.Right.freshSampling, PKE.Right.freshSamplingReal,
      FreshSampling.ofLabelBoundedProgram, FreshSampling.ofProgram, FreshSampling.parallel,
      FreshSampling.source, Distribution.ProbDist.single]
  · rintro ⟨_ | keys, ⟨⟩, ⟨⟩⟩ x
    · -- Both sample the keys at the first query.
      refine (PKE.Right.outcome_bindK (PKE.Real.freshStep pke) none (none, ((), ())) pke.gen.1
        (fun keys => (some keys, ((), ()))) (PKE.Real.outcome_none pke) x).trans ?_
      rw [PKE.LORCPA.Right.outcome_none, fTransform_bindK]
      exact bindK_congr fun keys _ => hsome none keys x
    · exact hsome (some ()) keys x
  · rw [fTransform_single]
    rfl

omit [DecidableEq C₂] in
/-- **`Left` of `OTS` is `Left` on the one-time encryption system** with uniform keys. -/
lemma Encryption.OTSLeft.eq_real (dem : SymmetricEncryption K M C₂) (q : LeftRight.Port → ℕ) :
    (Encryption.OTSLeft.perPort dem : Resource (LeftRight.perPort M C₂ q)) =
      Encryption.Left.perPort M C₂ • Encryption.OneTime.perPort { dem with gen := 𝒰[K] } := by
  -- `Left` on the one-time encryption system steps as `Left` of `OTS`.
  have hstep : ∀ (co : Option Unit) (x : Σ o, LeftRight.Input M o),
      ((Encryption.Left.body M C₂).probCombine
          (Encryption.OneTime.freshStep { dem with gen := 𝒰[K] })
          (Encryption.Left.bound_spec M C₂)).outcome (co, (co, ((), ()))) x =
        fTransform (Prod.map (fun s => (s.1, (s.1, ((), ())))) id)
          ((Encryption.OTSLeft.freshStep dem).outcome (co, ((), ())) x) := by
    rintro co ⟨o, mL, mR⟩
    cases o
    rw [Encryption.Left.outcome_enc _ co _ mL mR (bindK (𝒰[K]).1 fun k =>
        bindK dem.encryptions.1 fun E => Finsupp.single ((some (), ((), ())), E (k, mL)) 1)
        (by
          rw [Encryption.OneTime.outcome_enc, bindK_bindK]
          refine bindK_congr fun k _ => ?_
          rw [bindK_bindK]
          exact bindK_congr fun E _ => by rw [bindK_single, one_smul]),
      Encryption.OTSLeft.outcome_enc, fTransform_bindK, bindK_bindK]
    refine bindK_congr fun k _ => ?_
    rw [fTransform_bindK, bindK_bindK]
    refine bindK_congr fun E _ => ?_
    rw [bindK_single, one_smul, fTransform_single]
    rfl
  refine (Encryption.OTSLeft.freshSampling dem q).eq_fresh.trans
    (Eq.trans ?_ (Encryption.Left.freshSamplingOneTime { dem with gen := 𝒰[K] } q).eq_fresh.symm)
  refine Resource.ofProbAutomaton_eq_of_map _ _ _ _ (fun s => (s.1, (s.1, ((), ())))) ?_ ?_ <;>
    dsimp only [Encryption.OTSLeft.freshSampling, Encryption.Left.freshSamplingOneTime,
      FreshSampling.ofPreservingProgram, FreshSampling.ofProgram, FreshSampling.parallel,
      FreshSampling.source, Distribution.ProbDist.single, id]
  · rintro ⟨co, ⟨⟩, ⟨⟩⟩ x
    exact hstep co x
  · rw [fTransform_single]

omit [DecidableEq C₂] in
/-- **`Right` of `OTS` is `Right` on the one-time encryption system** with uniform keys. -/
lemma Encryption.OTSRight.eq_real (dem : SymmetricEncryption K M C₂) (q : LeftRight.Port → ℕ) :
    (Encryption.OTSRight.perPort dem : Resource (LeftRight.perPort M C₂ q)) =
      Encryption.Right.perPort M C₂ • Encryption.OneTime.perPort { dem with gen := 𝒰[K] } := by
  -- `Right` on the one-time encryption system steps as `Right` of `OTS`.
  have hstep : ∀ (co : Option Unit) (x : Σ o, LeftRight.Input M o),
      ((Encryption.Right.body M C₂).probCombine
          (Encryption.OneTime.freshStep { dem with gen := 𝒰[K] })
          (Encryption.Right.bound_spec M C₂)).outcome (co, (co, ((), ()))) x =
        fTransform (Prod.map (fun s => (s.1, (s.1, ((), ())))) id)
          ((Encryption.OTSRight.freshStep dem).outcome (co, ((), ())) x) := by
    rintro co ⟨o, mL, mR⟩
    cases o
    rw [Encryption.Right.outcome_enc _ co _ mL mR (bindK (𝒰[K]).1 fun k =>
        bindK dem.encryptions.1 fun E => Finsupp.single ((some (), ((), ())), E (k, mR)) 1)
        (by
          rw [Encryption.OneTime.outcome_enc, bindK_bindK]
          refine bindK_congr fun k _ => ?_
          rw [bindK_bindK]
          exact bindK_congr fun E _ => by rw [bindK_single, one_smul]),
      Encryption.OTSRight.outcome_enc, fTransform_bindK, bindK_bindK]
    refine bindK_congr fun k _ => ?_
    rw [fTransform_bindK, bindK_bindK]
    refine bindK_congr fun E _ => ?_
    rw [bindK_single, one_smul, fTransform_single]
    rfl
  refine (Encryption.OTSRight.freshSampling dem q).eq_fresh.trans
    (Eq.trans ?_ (Encryption.Right.freshSamplingOneTime { dem with gen := 𝒰[K] } q).eq_fresh.symm)
  refine Resource.ofProbAutomaton_eq_of_map _ _ _ _ (fun s => (s.1, (s.1, ((), ())))) ?_ ?_ <;>
    dsimp only [Encryption.OTSRight.freshSampling, Encryption.Right.freshSamplingOneTime,
      FreshSampling.ofPreservingProgram, FreshSampling.ofProgram, FreshSampling.parallel,
      FreshSampling.source, Distribution.ProbDist.single, id]
  · rintro ⟨co, ⟨⟩, ⟨⟩⟩ x
    exact hstep co x
  · rw [fTransform_single]

end Presentations

/-! ### Maps of states -/

/-- **The state of `R2(K) • OTS` of a state of `R1(E)` or `R3(E)` on `KEM-ideal`**: the keys of
the KEM, and the one-time game initialized once an encapsulation is recorded. -/
def state𝓡ₒ (s : Option Unit × ((Option (List (C₁ × K)) × (Option (PK × SK) × Unit × Unit) × Unit) ×
    Unit)) : Option (PK × SK) × ((Option Unit × Unit × Unit) × Unit × Unit) :=
  (s.2.1.2.1.1, ((if s.2.1.1.getD [] = [] then none else some (), ((), ())), ((), ())))

/-! ### The sequence of games -/

omit [DecidableEq SK] [DecidableEq C₂] [Nonempty K] in
/-- **`R1(E)` on `KEM-real` steps as `Left`** once the KEM is initialized, the state of the
KEM kept. -/
lemma R1.outcome_real (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (cR : Option Unit) (keys : PK × SK) (x : Σ o, PKELeftRight.Input M o) :
    (PKE.LORCPA.Left.freshStep (scheme kem dem)).outcome (some keys, ((), ())) x =
      fTransform (Prod.map (fun s => (s.2.1.1, ((), ()))) id)
        ((R1.freshStep dem (KEM.Real.freshStep kem)).outcome
          (cR, ((some keys, ((), ())), ())) x) := by
  obtain ⟨o, u⟩ := x
  cases o
  · obtain ⟨⟩ := u
    rw [PKE.LORCPA.Left.outcome_publicKey, R1.outcome_publicKey _ dem cR _ _ _
      (KEM.Real.outcome_publicKey kem keys), fTransform_single]
    rfl
  · -- A KEM + DEM encryption is an encapsulation and a DEM encryption under its key.
    obtain ⟨mL, mR⟩ := u
    rw [PKE.LORCPA.Left.outcome_enc, R1.outcome_enc _ dem cR _
      (bindK kem.encapsulations.1 fun e => Finsupp.single ((some keys, ((), ())), e keys.1) 1)
      (by rw [KEM.Real.outcome_encaps]; simp only [bindK_bindK, bindK_single, one_smul]),
      PublicKeyEncryption.bindK_encryptions (scheme kem dem) keys.1 mL
        (fun c => Finsupp.single ((some keys, ((), ())),
          (⟨.enc, c⟩ : Σ o, PKELeftRight.Output PK (C₁ × C₂) o)) 1)]
    simp only [bindK_bindK, bindK_single, one_smul, fTransform_bindK, fTransform_single]
    rw [KEM.bindK_encapsulations kem keys.1 (fun ck => bindK dem.encryptions.1 fun E =>
      Finsupp.single (Prod.map (fun s => (s.2.1.1, ((), ()))) id
        ((some (), ((some keys, ((), ())), ())),
          (⟨.enc, (ck.1, E (ck.2, mL))⟩ : Σ o, PKELeftRight.Output PK (C₁ × C₂) o))) 1)]
    dsimp only [scheme]
    rw [Distribution.ProbDist.bind_val, bindK_bindK]
    refine bindK_congr fun ck _ => ?_
    rw [show (Distribution.ProbDist.map (fun c₂ => (ck.1, c₂)) (dem.enc ck.2 mL)).1 =
        fTransform (fun c₂ => (ck.1, c₂)) (dem.enc ck.2 mL).1 from rfl, bindK_fTransform,
      SymmetricEncryption.bindK_encryptions dem ck.2 mL (fun c₂ => Finsupp.single
        (Prod.map (fun s => (s.2.1.1, ((), ()))) id ((some (), ((some keys, ((), ())), ())),
          (⟨.enc, (ck.1, c₂)⟩ : Σ o, PKELeftRight.Output PK (C₁ × C₂) o))) 1)]
    rfl

omit [DecidableEq SK] [DecidableEq C₂] [Nonempty K] in
/-- **`Left = R1(E) • KEM-real`** [2, 3]: encrypting `m_L` with KEM + DEM is encapsulating, and
encrypting `m_L` under the encapsulated key. -/
theorem left_eq_R1 (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (q : PKELeftRight.Port → ℕ) :
    (PKE.LORCPA.Left.perPort (scheme kem dem) : Resource (PKELeftRight.perPort PK M (C₁ × C₂) q)) =
      R1.perLabel PK C₁ dem q • KEM.Real.perPort kem := by
  refine (PKE.LORCPA.Left.freshSampling (scheme kem dem) q).eq_fresh.trans
    (Eq.trans ?_ (R1.freshSampling dem q (KEM.Real.freshSampling kem _)).eq_fresh.symm)
  symm
  refine Resource.ofProbAutomaton_eq_of_map _ _ _ _ (fun s => (s.2.1.1, ((), ()))) ?_ ?_ <;>
    dsimp only [PKE.LORCPA.Left.freshSampling, R1.freshSampling, KEM.Real.freshSampling,
      FreshSampling.ofRightContext, FreshSampling.cast, FreshSampling.ofProgram,
      FreshSampling.ofLabelBoundedProgram, FreshSampling.parallel, FreshSampling.source,
      Distribution.ProbDist.single]
  · rintro ⟨cR, ⟨_ | keys, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩ x
    · -- Both generate the keys at the first query.
      rw [PKE.LORCPA.Left.outcome_none, R1.outcome_bindK (KEM.Real.freshStep kem) dem cR
        (none, ((), ())) kem.gen.1 (fun keys => (some keys, ((), ())))
        (KEM.Real.outcome_none kem _) (KEM.Real.outcome_none kem _), fTransform_bindK]
      exact bindK_congr fun keys _ => R1.outcome_real kem dem cR keys x
    · exact R1.outcome_real kem dem cR keys x
  · rw [fTransform_single]

omit [DecidableEq SK] [DecidableEq C₂] in
/-- **`R1(E)` on `KEM-ideal` steps as `R2(K)` on `OTS-Left`** once the KEM is initialized,
along `state𝓡ₒ`. -/
lemma R1.outcome_ideal (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (cR : Option Unit) (cC : Option (List (C₁ × K))) (keys : PK × SK)
    (x : Σ o, PKELeftRight.Input M o) :
    (𝓡ₒ.freshStep kem (Encryption.OTSLeft.freshStep dem)).outcome
        (state𝓡ₒ (cR, ((cC, ((some keys, ((), ())), ())), ()))) x =
      fTransform (Prod.map state𝓡ₒ id)
        ((R1.freshStep dem (KEM.CCA.freshStep (KEM.Real.freshStep kem))).outcome
          (cR, ((cC, ((some keys, ((), ())), ())), ())) x) := by
  obtain ⟨o, u⟩ := x
  dsimp only [state𝓡ₒ]
  cases o
  · obtain ⟨⟩ := u
    rw [𝓡ₒ.outcome_publicKey, R1.outcome_publicKey _ dem cR _ _ _
      (KEM.CCA.outcome_publicKey _ cC _ _ _ (KEM.Real.outcome_publicKey kem keys)),
      fTransform_single]
    rfl
  · -- Both encrypt `m_L` under a uniform key, beside a real encapsulation.
    obtain ⟨mL, mR⟩ := u
    rw [𝓡ₒ.outcome_enc _ kem keys _ mL mR
        (bindK (𝒰[K]).1 fun k => bindK dem.encryptions.1 fun E =>
          Finsupp.single ((some (), ((), ())), E (k, mL)) 1)
        (by rw [Encryption.OTSLeft.outcome_enc]; simp only [bindK_bindK, bindK_single, one_smul]),
      R1.outcome_enc _ dem cR _
        (bindK kem.encapsulations.1 fun e => bindK (𝒰[K]).1 fun key =>
          Finsupp.single ((some (cC.getD [] ++ [((e keys.1).1, key)]), ((some keys, ((), ())), ())),
            ((e keys.1).1, key)) 1)
        (by
          rw [KEM.CCA.outcome_encaps _ cC _
            (bindK kem.encapsulations.1 fun e => Finsupp.single ((some keys, ((), ())), e keys.1) 1)
            (by rw [KEM.Real.outcome_encaps]; simp only [bindK_bindK, bindK_single, one_smul])]
          simp only [bindK_bindK, bindK_single, one_smul])]
    simp only [bindK_bindK, bindK_single, one_smul, fTransform_bindK, fTransform_single]
    refine bindK_congr fun e _ => bindK_congr fun k _ => bindK_congr fun E _ => ?_
    simp [state𝓡ₒ]

omit [DecidableEq SK] [DecidableEq C₂] in
/-- **`R1(E) • KEM-ideal = R2(K) • OTS-Left`** [2, 3]: encrypting `m_L` under the uniform key of
the ideal KEM is encrypting it under the fresh key of `OTS-Left`. -/
theorem R1_eq_𝓡ₒ (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (q : PKELeftRight.Port → ℕ) :
    R1.perLabel PK C₁ dem q • (KEM.CCA.perPort PK C₁ K • KEM.Real.perPort kem) =
      𝓡ₒ.perPort M C₂ kem • Encryption.OTSLeft.perPort dem := by
  refine (R1.freshSampling dem q
      (KEM.CCA.freshSampling (KEM.Real.freshSampling kem _))).eq_fresh.trans
    (Eq.trans ?_ (𝓡ₒ.freshSampling kem q (Encryption.OTSLeft.freshSampling dem _)).eq_fresh.symm)
  refine Resource.ofProbAutomaton_eq_of_map _ _ _ _ state𝓡ₒ ?_ ?_ <;>
    dsimp only [R1.freshSampling, KEM.CCA.freshSampling, KEM.Real.freshSampling,
      𝓡ₒ.freshSampling, Encryption.OTSLeft.freshSampling, FreshSampling.ofRightContext,
      FreshSampling.cast, FreshSampling.ofProgram, FreshSampling.ofPreservingProgram,
      FreshSampling.ofLabelBoundedProgram, FreshSampling.parallel, FreshSampling.source,
      Distribution.ProbDist.single]
  · rintro ⟨cR, ⟨cC, ⟨_ | keys, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩, ⟨⟩⟩ x
    · -- Both generate the keys at the first query.
      rw [R1.outcome_bindK (KEM.CCA.freshStep (KEM.Real.freshStep kem)) dem cR
        (cC, ((none, ((), ())), ())) kem.gen.1 (fun keys => (cC, ((some keys, ((), ())), ())))
        (KEM.CCA.outcome_bindK _ cC _ kem.gen.1 (fun keys => (some keys, ((), ())))
          ⟨.publicKey, ()⟩ (by simp) (KEM.Real.outcome_none kem _))
        (KEM.CCA.outcome_bindK _ cC _ kem.gen.1 (fun keys => (some keys, ((), ())))
          ⟨.encaps, ()⟩ (by simp) (KEM.Real.outcome_none kem _)), fTransform_bindK]
      dsimp only [state𝓡ₒ]
      rw [𝓡ₒ.outcome_none]
      exact bindK_congr fun keys _ => R1.outcome_ideal kem dem cR cC keys x
    · exact R1.outcome_ideal kem dem cR cC keys x
  · rw [fTransform_single]
    simp [state𝓡ₒ]

omit [DecidableEq SK] [DecidableEq C₂] in
/-- **`R3(E)` on `KEM-ideal` steps as `R2(K)` on `OTS-Right`** once the KEM is initialized,
along `state𝓡ₒ`. -/
lemma R3.outcome_ideal (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (cR : Option Unit) (cC : Option (List (C₁ × K))) (keys : PK × SK)
    (x : Σ o, PKELeftRight.Input M o) :
    (𝓡ₒ.freshStep kem (Encryption.OTSRight.freshStep dem)).outcome
        (state𝓡ₒ (cR, ((cC, ((some keys, ((), ())), ())), ()))) x =
      fTransform (Prod.map state𝓡ₒ id)
        ((R3.freshStep dem (KEM.CCA.freshStep (KEM.Real.freshStep kem))).outcome
          (cR, ((cC, ((some keys, ((), ())), ())), ())) x) := by
  obtain ⟨o, u⟩ := x
  dsimp only [state𝓡ₒ]
  cases o
  · obtain ⟨⟩ := u
    rw [𝓡ₒ.outcome_publicKey, R3.outcome_publicKey _ dem cR _ _ _
      (KEM.CCA.outcome_publicKey _ cC _ _ _ (KEM.Real.outcome_publicKey kem keys)),
      fTransform_single]
    rfl
  · -- Both encrypt `m_R` under a uniform key, beside a real encapsulation.
    obtain ⟨mL, mR⟩ := u
    rw [𝓡ₒ.outcome_enc _ kem keys _ mL mR
        (bindK (𝒰[K]).1 fun k => bindK dem.encryptions.1 fun E =>
          Finsupp.single ((some (), ((), ())), E (k, mR)) 1)
        (by rw [Encryption.OTSRight.outcome_enc]; simp only [bindK_bindK, bindK_single, one_smul]),
      R3.outcome_enc _ dem cR _
        (bindK kem.encapsulations.1 fun e => bindK (𝒰[K]).1 fun key =>
          Finsupp.single ((some (cC.getD [] ++ [((e keys.1).1, key)]), ((some keys, ((), ())), ())),
            ((e keys.1).1, key)) 1)
        (by
          rw [KEM.CCA.outcome_encaps _ cC _
            (bindK kem.encapsulations.1 fun e => Finsupp.single ((some keys, ((), ())), e keys.1) 1)
            (by rw [KEM.Real.outcome_encaps]; simp only [bindK_bindK, bindK_single, one_smul])]
          simp only [bindK_bindK, bindK_single, one_smul])]
    simp only [bindK_bindK, bindK_single, one_smul, fTransform_bindK, fTransform_single]
    refine bindK_congr fun e _ => bindK_congr fun k _ => bindK_congr fun E _ => ?_
    simp [state𝓡ₒ]

omit [DecidableEq SK] [DecidableEq C₂] in
/-- **`R3(E) • KEM-ideal = R2(K) • OTS-Right`** [2, 3]: encrypting `m_R` under the uniform key of
the ideal KEM is encrypting it under the fresh key of `OTS-Right`. -/
theorem R3_eq_𝓡ₒ (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (q : PKELeftRight.Port → ℕ) :
    R3.perLabel PK C₁ dem q • (KEM.CCA.perPort PK C₁ K • KEM.Real.perPort kem) =
      𝓡ₒ.perPort M C₂ kem • Encryption.OTSRight.perPort dem := by
  refine (R3.freshSampling dem q
      (KEM.CCA.freshSampling (KEM.Real.freshSampling kem _))).eq_fresh.trans
    (Eq.trans ?_ (𝓡ₒ.freshSampling kem q (Encryption.OTSRight.freshSampling dem _)).eq_fresh.symm)
  refine Resource.ofProbAutomaton_eq_of_map _ _ _ _ state𝓡ₒ ?_ ?_ <;>
    dsimp only [R3.freshSampling, KEM.CCA.freshSampling, KEM.Real.freshSampling,
      𝓡ₒ.freshSampling, Encryption.OTSRight.freshSampling, FreshSampling.ofRightContext,
      FreshSampling.cast, FreshSampling.ofProgram, FreshSampling.ofPreservingProgram,
      FreshSampling.ofLabelBoundedProgram, FreshSampling.parallel, FreshSampling.source,
      Distribution.ProbDist.single]
  · rintro ⟨cR, ⟨cC, ⟨_ | keys, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩, ⟨⟩⟩ x
    · -- Both generate the keys at the first query.
      rw [R3.outcome_bindK (KEM.CCA.freshStep (KEM.Real.freshStep kem)) dem cR
        (cC, ((none, ((), ())), ())) kem.gen.1 (fun keys => (cC, ((some keys, ((), ())), ())))
        (KEM.CCA.outcome_bindK _ cC _ kem.gen.1 (fun keys => (some keys, ((), ())))
          ⟨.publicKey, ()⟩ (by simp) (KEM.Real.outcome_none kem _))
        (KEM.CCA.outcome_bindK _ cC _ kem.gen.1 (fun keys => (some keys, ((), ())))
          ⟨.encaps, ()⟩ (by simp) (KEM.Real.outcome_none kem _)), fTransform_bindK]
      dsimp only [state𝓡ₒ]
      rw [𝓡ₒ.outcome_none]
      exact bindK_congr fun keys _ => R3.outcome_ideal kem dem cR cC keys x
    · exact R3.outcome_ideal kem dem cR cC keys x
  · rw [fTransform_single]
    simp [state𝓡ₒ]

omit [DecidableEq SK] [DecidableEq C₂] [Nonempty K] in
/-- **`R3(E)` on `KEM-real` steps as `Right`** once the KEM is initialized, the state of the
KEM kept. -/
lemma R3.outcome_real (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (cR : Option Unit) (keys : PK × SK) (x : Σ o, PKELeftRight.Input M o) :
    (PKE.LORCPA.Right.freshStep (scheme kem dem)).outcome (some keys, ((), ())) x =
      fTransform (Prod.map (fun s => (s.2.1.1, ((), ()))) id)
        ((R3.freshStep dem (KEM.Real.freshStep kem)).outcome
          (cR, ((some keys, ((), ())), ())) x) := by
  obtain ⟨o, u⟩ := x
  cases o
  · obtain ⟨⟩ := u
    rw [PKE.LORCPA.Right.outcome_publicKey, R3.outcome_publicKey _ dem cR _ _ _
      (KEM.Real.outcome_publicKey kem keys), fTransform_single]
    rfl
  · -- A KEM + DEM encryption is an encapsulation and a DEM encryption under its key.
    obtain ⟨mL, mR⟩ := u
    rw [PKE.LORCPA.Right.outcome_enc, R3.outcome_enc _ dem cR _
      (bindK kem.encapsulations.1 fun e => Finsupp.single ((some keys, ((), ())), e keys.1) 1)
      (by rw [KEM.Real.outcome_encaps]; simp only [bindK_bindK, bindK_single, one_smul]),
      PublicKeyEncryption.bindK_encryptions (scheme kem dem) keys.1 mR
        (fun c => Finsupp.single ((some keys, ((), ())),
          (⟨.enc, c⟩ : Σ o, PKELeftRight.Output PK (C₁ × C₂) o)) 1)]
    simp only [bindK_bindK, bindK_single, one_smul, fTransform_bindK, fTransform_single]
    rw [KEM.bindK_encapsulations kem keys.1 (fun ck => bindK dem.encryptions.1 fun E =>
      Finsupp.single (Prod.map (fun s => (s.2.1.1, ((), ()))) id
        ((some (), ((some keys, ((), ())), ())),
          (⟨.enc, (ck.1, E (ck.2, mR))⟩ : Σ o, PKELeftRight.Output PK (C₁ × C₂) o))) 1)]
    dsimp only [scheme]
    rw [Distribution.ProbDist.bind_val, bindK_bindK]
    refine bindK_congr fun ck _ => ?_
    rw [show (Distribution.ProbDist.map (fun c₂ => (ck.1, c₂)) (dem.enc ck.2 mR)).1 =
        fTransform (fun c₂ => (ck.1, c₂)) (dem.enc ck.2 mR).1 from rfl, bindK_fTransform,
      SymmetricEncryption.bindK_encryptions dem ck.2 mR (fun c₂ => Finsupp.single
        (Prod.map (fun s => (s.2.1.1, ((), ()))) id ((some (), ((some keys, ((), ())), ())),
          (⟨.enc, (ck.1, c₂)⟩ : Σ o, PKELeftRight.Output PK (C₁ × C₂) o))) 1)]
    rfl

omit [DecidableEq SK] [DecidableEq C₂] [Nonempty K] in
/-- **`Right = R3(E) • KEM-real`** [2, 3]: encrypting `m_R` with KEM + DEM is encapsulating, and
encrypting `m_R` under the encapsulated key. -/
theorem right_eq_R3 (kem : KEM PK SK C₁ K) (dem : SymmetricEncryption K M C₂)
    (q : PKELeftRight.Port → ℕ) :
    (PKE.LORCPA.Right.perPort (scheme kem dem) : Resource (PKELeftRight.perPort PK M (C₁ × C₂) q)) =
      R3.perLabel PK C₁ dem q • KEM.Real.perPort kem := by
  refine (PKE.LORCPA.Right.freshSampling (scheme kem dem) q).eq_fresh.trans
    (Eq.trans ?_ (R3.freshSampling dem q (KEM.Real.freshSampling kem _)).eq_fresh.symm)
  symm
  refine Resource.ofProbAutomaton_eq_of_map _ _ _ _ (fun s => (s.2.1.1, ((), ()))) ?_ ?_ <;>
    dsimp only [PKE.LORCPA.Right.freshSampling, R3.freshSampling, KEM.Real.freshSampling,
      FreshSampling.ofRightContext, FreshSampling.cast, FreshSampling.ofProgram,
      FreshSampling.ofLabelBoundedProgram, FreshSampling.parallel, FreshSampling.source,
      Distribution.ProbDist.single]
  · rintro ⟨cR, ⟨_ | keys, ⟨⟩, ⟨⟩⟩, ⟨⟩⟩ x
    · -- Both generate the keys at the first query.
      rw [PKE.LORCPA.Right.outcome_none, R3.outcome_bindK (KEM.Real.freshStep kem) dem cR
        (none, ((), ())) kem.gen.1 (fun keys => (some keys, ((), ())))
        (KEM.Real.outcome_none kem _) (KEM.Real.outcome_none kem _), fTransform_bindK]
      exact bindK_congr fun keys _ => R3.outcome_real kem dem cR keys x
    · exact R3.outcome_real kem dem cR keys x
  · rw [fTransform_single]

omit [DecidableEq SK] [DecidableEq C₂] in
/-- **The CPA variant** [1, §3.1], in the many-challenge form of [2, 3]: KEM IND-CPA within `εkem`
and one-time DEM security within `εots` give left-or-right CPA security of KEM + DEM within the
losses at `R1(E)`, `R2(K)` and `R3(E)`. -/
theorem kem_dem_cpa [AdmissibleDistinguishers] (kem : KEM PK SK C₁ K)
    (dem : SymmetricEncryption K M C₂) {q : PKELeftRight.Port → ℕ}
    (εkem : (Encapsulation.perPort PK C₁ K
      (Function.update (kemBudget q) .decaps 0)).inputDomain.DistinguisherBehavior → ENNReal)
    (εots :
      (LeftRight.perPort M C₂ (𝓡ₒ.insideBudget M C₂ kem q)).inputDomain.DistinguisherBehavior →
        ENNReal)
    (kemSecure : KEM.INDCPA kem εkem) (otsSecure : Encryption.OTS dem εots) :
    PKE.LORCPA (scheme kem dem) fun D =>
      εkem (absorb (R1.perLabel PK C₁ dem q) D) + εots (absorb (𝓡ₒ.perPort M C₂ kem) D) +
        εkem (absorb (R3.perLabel PK C₁ dem q) D) := by
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    PKE.Left.perLabel PK M (C₁ × C₂) q • PKE.Real.perPort (scheme kem dem) =
        PKE.LORCPA.Left.perPort (scheme kem dem) :=
      (PKE.LORCPA.Left.eq_real (scheme kem dem) q).symm
    _ = R1.perLabel PK C₁ dem q • KEM.Real.perPort kem := left_eq_R1 kem dem q
    _ ≃[εkem ∘ absorb (R1.perLabel PK C₁ dem q)]
        R1.perLabel PK C₁ dem q • (KEM.CCA.perPort PK C₁ K • KEM.Real.perPort kem) :=
      AdmissibleDistinguishers.substitutesWithin_attach _ kemSecure
    _ = 𝓡ₒ.perPort M C₂ kem • Encryption.OTSLeft.perPort dem := R1_eq_𝓡ₒ kem dem q
    _ = 𝓡ₒ.perPort M C₂ kem •
        (Encryption.Left.perPort M C₂ • Encryption.OneTime.perPort { dem with gen := 𝒰[K] }) := by
      rw [Encryption.OTSLeft.eq_real]
    _ ≃[εots ∘ absorb (𝓡ₒ.perPort M C₂ kem)]
        𝓡ₒ.perPort M C₂ kem •
          (Encryption.Right.perPort M C₂ • Encryption.OneTime.perPort { dem with gen := 𝒰[K] }) :=
      AdmissibleDistinguishers.substitutesWithin_attach _ otsSecure
    _ = 𝓡ₒ.perPort M C₂ kem • Encryption.OTSRight.perPort dem := by
      rw [Encryption.OTSRight.eq_real]
    _ = R3.perLabel PK C₁ dem q • (KEM.CCA.perPort PK C₁ K • KEM.Real.perPort kem) :=
      (R3_eq_𝓡ₒ kem dem q).symm
    _ ≃[εkem ∘ absorb (R3.perLabel PK C₁ dem q)] R3.perLabel PK C₁ dem q • KEM.Real.perPort kem :=
      AdmissibleDistinguishers.substitutesWithin_attach _
        (DistinguisherAdvantage.SubstitutesWithin.symm _ kemSecure)
    _ = PKE.LORCPA.Right.perPort (scheme kem dem) := (right_eq_R3 kem dem q).symm
    _ = PKE.Right.perLabel PK M (C₁ × C₂) q • PKE.Real.perPort (scheme kem dem) :=
      PKE.LORCPA.Right.eq_real (scheme kem dem) q

end

end ProofLadders.KEMDEM
