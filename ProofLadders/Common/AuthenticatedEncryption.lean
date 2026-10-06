import Commons.Definitions.AEAD
import ConstructiveCryptography.Tactics.Substitution
import ProofLadders.Common.ProbAutomaton

/-!
# Authenticated encryption from ind-cpa and int-ctxt

Banfi, Theorem 2.3.10(3) [1]: `(ind-cpa, int-ctxt) → ae`, with one use of each assumption. The
chain substitutes `ρ^ctxt(E_k)` for `⟦E_k, D_k⟧` by int-ctxt, then `ρ^ctxt ∘ ρ^cpa(E_k)` for
`ρ^ctxt(E_k)` by ind-cpa inside `ρ^ctxt`, and ends with `ρ^ctxt ∘ ρ^cpa = ρ^ae`. [1] takes this
last step as the definition of `ρ^ae`. Here `ρ^ae` is the Commons converter `AE.Ideal`, so the
step is an equality of systems: replacing each message by a random one and then recording it
with its ciphertext is the ideal transformation.

The equality is a map of states between fresh-sampling automata. `ρ^cpa`, `ρ^ctxt` and `ρ^ae`
are characterized once as steps on any inside probabilistic step: `ρ^cpa` samples a replacement
message and encrypts it, `ρ^ctxt` encrypts and records the pair, `ρ^ae` does both, and decryption
replays the table. Both sides present `E_k` the same way, so the map forgets the state of
`ρ^cpa`.

Upstream candidates: `ctxt_cpa_eq_ideal` and `ae_of_ind_cpa_int_ctxt`, for
`Examples.AuthenticatedEncryption.Security` beside `ae_of_ind_cca_int_ptxt`; the step lemmas and
fresh-sampling presentations, for `Commons.Definitions.AEAD`.

## Main definitions

* `Encryption.Real.freshSampling`, `Encryption.CPA.freshSamplingReal`,
  `AE.CTXT.freshSamplingCPA`, `AE.Ideal.freshSamplingReal`: `E_k`, `ρ^cpa(E_k)`,
  `ρ^ctxt ∘ ρ^cpa(E_k)` and `ρ^ae(E_k)` as fresh sampling

## Main results

* `Encryption.CPA.outcome_enc`, `AE.CTXT.outcome_enc`, `AE.CTXT.outcome_dec`,
  `AE.Ideal.outcome_enc`, `AE.Ideal.outcome_dec`: the transformations as steps
* `ctxt_cpa_eq_ideal`: `ρ^ctxt ∘ ρ^cpa(E_k) = ρ^ae(E_k)`
* `ae_of_ind_cpa_int_ctxt`: `(ind-cpa, int-ctxt) → ae`

## References

1. F. Banfi. *Cryptographic Security Notions as Substitutions*. PhD thesis, ETH Zürich, 2023.
-/

namespace Commons

open Probability Probability.Distribution SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface
open ConstructiveCryptography.CryptographicAlgebra
open scoped SystemAlgebra

section Steps

variable {M C R : Type} [Fintype M] [Fintype C] [Nonempty M]

/-- **`ρ^cpa` on a probabilistic step**: sample a replacement message and encrypt it. -/
lemma Encryption.CPA.outcome_enc
    (stepR : ProbStep R Encryption.Port (Encryption.Input M) (Encryption.Output C))
    (c : Option Unit) (r : R) (m : M) :
    ((Encryption.CPA.body M C).probCombine
        (ProbStep.parallel stepR (ProbStep.fresh (Encryption.CPA.law1 M C)))
        (Encryption.CPA.bound_spec M C)).outcome (c, (r, ())) ⟨.enc, m⟩ =
      bindK (Encryption.CPA.law1 M C).1 fun m' =>
        fTransform (fun p => ((some (), (p.1, ())), p.2)) (stepR.outcome r ⟨.enc, m'⟩) := by
  rw [ProbStep.outcome, Program.probCombine_val]
  have h0 : (Encryption.CPA.body M C) c .enc m [] = .inr ⟨.inr (), ()⟩ := by
    cases c <;> rfl
  rw [show Encryption.CPA.bound M C = 1 + 1 from rfl, Program.probInvoke_succ_inr h0]
  dsimp only
  rw [ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, fTransform_fTransform, bindK_fTransform,
    Function.comp_def, fTransform_bindK]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_succ_inr (q := ⟨.inl .enc, z⟩)
      (by cases c <;> simp [Encryption.CPA.body, callProg, ProbStep.inrReply, ProbStep.tagged]),
    ProbStep.outcome_parallel_inl]
  simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def, fTransform_bindK]
  conv_rhs => rw [fTransform_eq_bindK]
  refine bindK_congr fun y _ => ?_
  rw [Program.probInvoke_inl (a := (some (), y.2))
    (by cases c <;> simp [Encryption.CPA.body, callProg, returnProg, ProbStep.inrReply,
      ProbStep.inlReply, ProbStep.tagged])]
  simp [fTransform, ProbStep.tagged]

/-- The ciphertext of an encryption reply. -/
def Encryption.ciphertextOf : (Σ j, Encryption.Output C j) → C
  | ⟨.enc, c⟩ => c

variable [DecidableEq C]

omit [Nonempty M] in
/-- **`ρ^ctxt` on encryption**: encrypt through the inside step and record the pair. -/
lemma AE.CTXT.outcome_enc
    (stepR : ProbStep R Encryption.Port (Encryption.Input M) (Encryption.Output C))
    (c : Option (List (M × C))) (r : R) (m : M) :
    ((AE.CTXT.body M C).probCombine stepR (AE.CTXT.bound_spec M C)).outcome (c, r) ⟨.enc, m⟩ =
      fTransform (fun p => ((some (c.getD [] ++ [(m, Encryption.ciphertextOf p.2)]), p.1),
        (⟨.enc, Encryption.ciphertextOf p.2⟩ : Σ o, AE.Output M C o)))
        (stepR.outcome r ⟨.enc, m⟩) := by
  rw [ProbStep.outcome, Program.probCombine_val]
  rw [show AE.CTXT.bound M C = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.enc, m⟩) (by cases c <;> simp [AE.CTXT.body, callProg])]
  simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def, fTransform_bindK,
    fTransform_fTransform]
  conv_rhs => rw [fTransform_eq_bindK]
  refine bindK_congr fun y _ => ?_
  rw [Program.probInvoke_inl
    (a := ((some (c.getD [] ++ [(m, y.2)]), y.2) : _ × AE.Output M C AE.Port.enc))
    (by cases c <;> simp [AE.CTXT.body, callProg, returnProg, ProbStep.tagged])]
  simp [fTransform, ProbStep.tagged, Encryption.ciphertextOf]

omit [Nonempty M] in
/-- **`ρ^ctxt` on decryption**: replay from the table. -/
lemma AE.CTXT.outcome_dec
    (stepR : ProbStep R Encryption.Port (Encryption.Input M) (Encryption.Output C))
    (c : Option (List (M × C))) (r : R) (ct : C) :
    ((AE.CTXT.body M C).probCombine stepR (AE.CTXT.bound_spec M C)).outcome (c, r) ⟨.dec, ct⟩ =
      Finsupp.single ((some (c.getD []), r),
        (⟨.dec, AE.replay (c.getD []) ct⟩ : Σ o, AE.Output M C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (c.getD []), AE.replay (c.getD []) ct))
      (by cases c <;> simp [AE.CTXT.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

/-- **`ρ^ae` on encryption**: encrypt a replacement message and record the pair. -/
lemma AE.Ideal.outcome_enc
    (stepR : ProbStep R Encryption.Port (Encryption.Input M) (Encryption.Output C))
    (c : Option (List (M × C))) (r : R) (m : M) :
    ((AE.Ideal.body M C).probCombine
        (ProbStep.parallel stepR (ProbStep.fresh (AE.Ideal.law1 M C)))
        (AE.Ideal.bound_spec M C)).outcome (c, (r, ())) ⟨.enc, m⟩ =
      bindK (AE.Ideal.law1 M C).1 fun m' =>
        fTransform (fun p => ((some (c.getD [] ++ [(m, Encryption.ciphertextOf p.2)]),
          (p.1, ())), (⟨.enc, Encryption.ciphertextOf p.2⟩ : Σ o, AE.Output M C o)))
          (stepR.outcome r ⟨.enc, m'⟩) := by
  rw [ProbStep.outcome, Program.probCombine_val]
  rw [show AE.Ideal.bound M C = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
      (by cases c <;> simp [AE.Ideal.body, callProg])]
  dsimp only
  rw [ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, ProbStep.fresh, fTransform_fTransform, bindK_fTransform,
    Function.comp_def, fTransform_bindK]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_succ_inr (q := ⟨.inl .enc, z⟩)
      (by cases c <;> simp [AE.Ideal.body, callProg, ProbStep.inrReply, ProbStep.tagged]),
    ProbStep.outcome_parallel_inl]
  simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def, fTransform_bindK,
    fTransform_fTransform]
  conv_rhs => rw [fTransform_eq_bindK]
  refine bindK_congr fun y _ => ?_
  rw [Program.probInvoke_inl
    (a := ((some (c.getD [] ++ [(m, y.2)]), y.2) : _ × AE.Output M C AE.Port.enc))
    (by cases c <;> simp [AE.Ideal.body, callProg, returnProg, ProbStep.inrReply,
      ProbStep.inlReply, ProbStep.tagged])]
  simp [fTransform, ProbStep.tagged, Encryption.ciphertextOf]

/-- **`ρ^ae` on decryption**: replay from the table. -/
lemma AE.Ideal.outcome_dec
    (stepR : ProbStep R Encryption.Port (Encryption.Input M) (Encryption.Output C))
    (c : Option (List (M × C))) (r : R) (ct : C) :
    ((AE.Ideal.body M C).probCombine
        (ProbStep.parallel stepR (ProbStep.fresh (AE.Ideal.law1 M C)))
        (AE.Ideal.bound_spec M C)).outcome (c, (r, ())) ⟨.dec, ct⟩ =
      Finsupp.single ((some (c.getD []), (r, ())),
        (⟨.dec, AE.replay (c.getD []) ct⟩ : Σ o, AE.Output M C o)) 1 := by
  rw [ProbStep.outcome, Program.probCombine_val,
    Program.probInvoke_inl (a := (some (c.getD []), AE.replay (c.getD []) ct))
      (by cases c <;> simp [AE.Ideal.body, returnProg])]
  simp [fTransform, ProbStep.tagged]

end Steps

section FreshSampling

variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C] [DecidableEq K] [DecidableEq M]
  [DecidableEq C] [Nonempty M]

/-- `E_k` as fresh sampling. -/
noncomputable def Encryption.Real.freshSampling (scheme : SymmetricEncryption K M C)
    (q : Encryption.Port → ℕ) :
    FreshSampling (Encryption.perPort M C q) (Encryption.Real.perPort scheme) :=
  ((FreshSampling.source (Encryption.Real.law1 scheme) _).parallel
    (FreshSampling.source (Encryption.Real.law2 scheme) _)).ofProgram none _ _ _

/-- `ρ^cpa(E_k)` as fresh sampling. -/
noncomputable def Encryption.CPA.freshSamplingReal (scheme : SymmetricEncryption K M C)
    (q : Encryption.Port → ℕ) :
    FreshSampling (Encryption.perPort M C q) (ρ^cpa • Encryption.Real.perPort scheme) :=
  FreshSampling.ofRightContext _
    (((Encryption.Real.freshSampling scheme q).parallel
      (FreshSampling.source (Encryption.CPA.law1 M C) _)).ofPreservingProgram none _ _ _ _ _ _ _)

/-- `ρ^ctxt ∘ ρ^cpa(E_k)` as fresh sampling. -/
noncomputable def AE.CTXT.freshSamplingCPA (scheme : SymmetricEncryption K M C)
    (q : AE.Port → ℕ) :
    FreshSampling (AE.perPort M C q) (ρ^ctxt • ρ^cpa • Encryption.Real.perPort scheme) := by
  unfold AE.CTXT.perPort AE.CTXT.perPortProgram
  exact (Encryption.CPA.freshSamplingReal scheme (AE.CTXT.insideBudget M C q)).ofPreservingProgram
    none _ _ _ _ _ _ _

/-- `ρ^ae(E_k)` as fresh sampling. -/
noncomputable def AE.Ideal.freshSamplingReal (scheme : SymmetricEncryption K M C)
    (q : AE.Port → ℕ) :
    FreshSampling (AE.perPort M C q) (ρ^ae • Encryption.Real.perPort scheme) :=
  FreshSampling.ofRightContext _
    (((Encryption.Real.freshSampling scheme (AE.Ideal.insideBudget M C q)).parallel
      (FreshSampling.source (AE.Ideal.law1 M C) _)).ofPreservingProgram none _ _ _ _ _ _ _)

/-- **`ρ^ctxt ∘ ρ^cpa(E_k) = ρ^ae(E_k)`** [1, Theorem 2.3.10(3)]: recording each message with the
encryption of a random replacement message is the ideal transformation. -/
theorem ctxt_cpa_eq_ideal (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ) :
    (ρ^ctxt • ρ^cpa • Encryption.Real.perPort scheme : Resource (AE.perPort M C q)) =
      ρ^ae • Encryption.Real.perPort scheme := by
  refine (AE.CTXT.freshSamplingCPA scheme q).eq_fresh.trans
    (Eq.trans ?_ (AE.Ideal.freshSamplingReal scheme q).eq_fresh.symm)
  -- The two fresh-sampling automata agree once the state of `ρ^cpa` is forgotten.
  refine Resource.ofProbAutomaton_eq_of_map _ _ _ _ (fun s => (s.1, s.2.2)) ?_ ?_ <;>
    dsimp only [AE.Ideal.freshSamplingReal, AE.CTXT.freshSamplingCPA,
      Encryption.CPA.freshSamplingReal, Encryption.Real.freshSampling,
      FreshSampling.ofRightContext, FreshSampling.cast, FreshSampling.ofPreservingProgram,
      FreshSampling.ofProgram, FreshSampling.parallel, FreshSampling.source, id,
      Distribution.ProbDist.single]
  · rintro ⟨c, p, ⟨e, u⟩, ⟨⟩⟩ ⟨_ | _, x⟩
    · rw [AE.Ideal.outcome_enc, AE.CTXT.outcome_enc, Encryption.CPA.outcome_enc,
        fTransform_fTransform, fTransform_bindK]
      simp only [fTransform_fTransform, Function.comp_def]
      rfl
    · rw [AE.Ideal.outcome_dec, AE.CTXT.outcome_dec]
      simp [fTransform]
  · rw [fTransform_single]

/-- **`(ind-cpa, int-ctxt) → ae`** [1, Theorem 2.3.10(3)]: int-ctxt within `εctxt` and ind-cpa
within `εcpa` give ae within `εctxt` and `εcpa` at the distinguisher with `ρ^ctxt` absorbed. -/
theorem ae_of_ind_cpa_int_ctxt [AdmissibleDistinguishers] (scheme : SymmetricEncryption K M C)
    {q : AE.Port → ℕ} (εctxt : (AE.perPort M C q).inputDomain.DistinguisherBehavior → ENNReal)
    (εcpa :
      (Encryption.perPort M C (AE.CTXT.insideBudget M C q)).inputDomain.DistinguisherBehavior →
        ENNReal)
    (ctxt : AE.INTCTXT scheme εctxt) (cpa : Encryption.INDCPA scheme εcpa) :
    AE.Secure scheme fun D => εctxt D + εcpa (absorb ρ^ctxt D) := by
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    AE.Real.perPort scheme ≃[εctxt] ρ^ctxt • Encryption.Real.perPort scheme := ctxt
    _ ≃[εcpa ∘ absorb ρ^ctxt] ρ^ctxt • ρ^cpa • Encryption.Real.perPort scheme :=
      AdmissibleDistinguishers.substitutesWithin_context ρ^ctxt cpa
    _ = ρ^ae • Encryption.Real.perPort scheme := ctxt_cpa_eq_ideal scheme q

end FreshSampling

end Commons
