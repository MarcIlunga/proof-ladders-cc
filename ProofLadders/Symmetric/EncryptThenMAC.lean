import Commons.Definitions.MAC
import ProofLadders.Common.Encryption
import ProofLadders.Common.AuthenticatedEncryption
import ProofLadders.Common.Programs
import ProofLadders.Common.Probability

/-!
# Encrypt-then-MAC

The encrypt-then-MAC problem of the symmetric ladder, in its two statements:

* [1]: encrypt-then-MAC is IND-CPA and INT-CTXT, from the IND-CPA security of the encryption
  scheme and the SUF-CMA security of the MAC [2, 3]. IND-CPA and INT-CTXT are the Commons notions
  `Encryption.INDCPA` and `AE.INTCTXT`, SUF-CMA is `MAC.SUFCMA`. With Banfi's
  `(ind-cpa, int-ctxt) → ae`, it is ae, and the protocol `π_EtM` constructs the authenticated
  encryption of encrypt-then-MAC from the two schemes.
* [4, §5]: if `Σ_e` is CPA-secure and `Σ_m` is a secure MAC whose messages include the
  ciphertexts of `Σ_e`, then encrypt-then-MAC is CCA-secure, in the left-or-right form
  `Encryption.LORCCA`. CPA security is left-or-right, `cpa-left ≃ cpa-right` for the Commons
  converters `Encryption.Left` and `Encryption.Right`. The MAC libraries `mac-real` and
  `mac-fake` of [4] are `MAC.SUFCMA`, whose fake verification also checks the tag, which holds
  for every recorded pair of the real libraries.

`Σ` is reserved in Lean, so `Σ_e` is `scheme` and `Σ_m` is `mac`. The key `k_e ‖ k_m` is a pair of
independent keys of the two schemes.

Encrypt-then-MAC is the protocol `π_EtM` on the two schemes side by side: `⟦E_k, D_k⟧` of
encrypt-then-MAC is `π_EtM` attached to `⟦E_k, D_k⟧ ∥ ⟦S_k, V_k⟧` of `Σ_e` and `Σ_m`
(`real_eq`), and its encryption `E_k` is `π_enc` on `E_k ∥ ⟦S_k, V_k⟧` (`encryptionReal_eq`).
The statements of [1] are chains through these factorizations, the reductions being the
contexts of the substitutions: for INT-CTXT, `π_EtM` with `⟦E_k, D_k⟧` of `Σ_e` beside the MAC,
`real = π_EtM • (⟦E_k, D_k⟧ ∥ mac-real) ≃ π_EtM • (⟦E_k, D_k⟧ ∥ mac-fake) = ρ^ctxt(E_k)`
(`suf_eq_ctxt`: with the fake MAC only issued ciphertexts verify, and correctness decrypts
them); for IND-CPA, `π_enc` with the MAC beside the encryption,
`E_k = π_enc • (E_k ∥ mac-real) ≃ π_enc • (ρ^cpa(E_k) ∥ mac-real) = ρ^cpa(π_enc • (E_k ∥ mac-real))`
(`cpa_comm`: replacing the message before encrypting is replacing it before encrypt-then-MAC).

The four equalities are simulations of fresh-sampling automata. `encryptionReal_eq` and
`cpa_comm` are maps of states. `real_eq` defers the sampling of `k_e`, which `⟦E_k, D_k⟧` of
`Σ_e` samples at its first call, never made by a decryption that fails verification.
`suf_eq_ctxt` defers the sampling of `k_m`, which `mac-fake` samples at a verification before
the first encryption, on the invariant that the tagged pairs of `mac-fake` are the recorded
ciphertexts of `ρ^ctxt`, each an encryption and a tag under the keys.

The CCA statement of [4, §5] is the chain of [4] with its calling programs: `𝓜 b` encrypts the
message `m_b` itself and tags and verifies through the MAC, and `𝓒` tags the ciphertexts of the
CPA oracle and decrypts nothing: `cca-left = 𝓜 false • mac-real ≃ 𝓜 false • mac-fake =
𝓒 • cpa-left ≃ 𝓒 • cpa-right = 𝓜 true • mac-fake ≃ 𝓜 true • mac-real = cca-right`. Its two
equalities are simulations too. `cca_eq` splits the key `k_e ‖ k_m` of `cca-b` into the key `k_e`
of `𝓜 b` and the key `k_m` of `mac-real`. In `fake_eq` the tagged pairs of `mac-fake` are the
ciphertexts of `𝒟`, so a ciphertext outside `𝒟` never verifies and `𝓜 b` decrypts nothing;
`𝓒 • cpa-b` keeps no `𝒟`, so it is simulated with a record of its ciphertexts, along the kernel
that samples `k_e`, which `𝓜 b` samples at its first call, while `E_k` has not.

Upstream candidates: `ite_bindK`, `bindK_fTransform_comm`, and the steps with a record
`ProbStep.withRecord`, `ProbStep.outcome_withRecord` and
`Interface.Resource.ofProbAutomaton_withRecord`, for `Common.ProbAutomaton`; `keyLaw`,
`Encryption.val_eq_outcome`, the step lemmas of `E_k`, `⟦E_k, D_k⟧`, `⟦S_k, V_k⟧` and `mac-fake`
with `Encryption.Real.mem_support_step_enc`, and the fresh-sampling presentations
`AE.Real.freshSampling`, `MAC.Real.freshSampling`, `MAC.SUF.freshSamplingReal` and
`AE.CTXT.freshSamplingReal`, for `Common.AuthenticatedEncryption`; the step lemmas of `Left`,
`Right`, `cca-left` and `cca-right`, and their fresh-sampling presentations
`Encryption.Left.freshSamplingReal`, `Encryption.Right.freshSamplingReal`,
`Encryption.LeftCCA.freshSamplingReal` and `Encryption.RightCCA.freshSamplingReal`, for
`Common.Encryption`.

## Main definitions

* `EncryptThenMAC scheme mac`: the scheme
* `𝓟`, `𝓟.perLabel`: the protocol `π_EtM` on encryption and tagging, at per-port budgets
* `𝓟ₑ`, `𝓟ₑ.perLabel`: its encryption `π_enc`
* `𝓜 b`, `𝓒`: the calling programs of the CCA chain of [4]
* `𝓟.freshSamplingReal`, `𝓟.freshSamplingSUF`, `𝓟ₑ.freshSamplingReal`, `𝓟ₑ.freshSamplingCPA`,
  `cpaFreshSampling`, `𝓜.freshSampling`, `𝓒.freshSampling`: the compositions of the chains as
  fresh sampling
* `deferredKeys`, `ctxtKernel`, `ctxtInvariant`: the kernels of the deferred samplings, and the
  reachable states of `ρ^ctxt(E_k)`
* `ProbStep.withRecord`, `challengesAfter`: a step with a record, and `𝒟` as a record
* `ccaKernel`, `fakeKernel`, `fakeInvariant`: the kernels of the CCA chain, and the reachable
  states of `𝓒 • cpa-b` with `𝒟`

## Main results

* `𝓟.step_enc`, `𝓟.step_dec`, `𝓟ₑ.step_enc`: `π_EtM` and `π_enc` as steps
* `𝓜.step_enc`, `𝓜.step_dec`, `𝓒.step_enc`, `𝓒.step_dec`, `𝓒.mem_support_step`: `𝓜 b` and `𝓒`
  as steps
* `Interface.Resource.ofProbAutomaton_withRecord`: a record does not change the resource
* `replay_eq`: with correct schemes, replaying the table of `ρ^ctxt` decrypts the issued pairs
* `real_eq`, `encryptionReal_eq`: encrypt-then-MAC is the protocol on the two schemes
* `suf_eq_ctxt`, `cpa_comm`: the steps of the chains
* `cca_eq`, `fake_eq`: the steps of the CCA chain
* `encrypt_then_mac_ind_cpa`, `encrypt_then_mac_int_ctxt`: the statement of [1]
* `encrypt_then_mac_ae`, `encrypt_then_mac_constructs`: ae, and the construction
* `encrypt_then_mac_cca`: the statement of [4, §5]

## References

1. The symmetric proof ladder, `proof-ladders/symmetric-ladder`, `README.md` and
   `EtM-IND-CPA+CTXT`.
2. The symmetric proof ladder, encrypt-then-MAC in EasyCrypt, `EtM-IND-CPA+CTXT/EtM.eca`.
3. The symmetric proof ladder, encrypt-then-MAC in CryptoVerif,
   `EtM-IND-CPA+CTXT/enc-then-MAC-IND-CPA.ocv` and `enc-then-MAC-INT_CTXT.ocv`.
4. The symmetric proof ladder, *Security proofs in the style of The Joy of Cryptography*,
   `proof-ladders/symmetric-ladder`, `Notes/selfcontained.tex`.
-/

/-! ### Upstream candidates for `Common/ProbAutomaton` -/

namespace Probability.Distribution

/-- A mixture over a branch is the branch of the mixtures. -/
lemma ite_bindK {A B : Type} (p : Prop) [Decidable p] (μ ν : Distribution A)
    (f : A → Distribution B) :
    bindK (if p then μ else ν) f = if p then bindK μ f else bindK ν f := by
  split_ifs <;> rfl

/-- **Independent pushforwards commute.** -/
lemma bindK_fTransform_comm {A B C : Type} (μ : Distribution A) (ν : Distribution B)
    (f : A → B → C) :
    (bindK μ fun a => fTransform (f a) ν) = bindK ν fun b => fTransform (fun a => f a b) μ := by
  simp only [fTransform_eq_bindK]
  exact bindK_comm μ ν _

end Probability.Distribution

namespace SystemAlgebra

open Probability Probability.Distribution

/-- **A probabilistic step with a record**: the step, beside a record that each query and its
reply update by `g`. -/
noncomputable def ProbStep.withRecord {S I Z : Type} {X Y : I → Type} (step : ProbStep S I X Y)
    (g : Z → (Σ i, X i) → (Σ i, Y i) → Z) : ProbStep (S × Z) I X Y :=
  fun sz i x =>
    Distribution.ProbDist.map (fun sy => ((sy.1, g sz.2 ⟨i, x⟩ ⟨i, sy.2⟩), sy.2)) (step sz.1 i x)

/-- A step with a record is the step, with the record updated by the query and the reply. -/
lemma ProbStep.outcome_withRecord {S I Z : Type} {X Y : I → Type} (step : ProbStep S I X Y)
    (g : Z → (Σ i, X i) → (Σ i, Y i) → Z) (s : S) (z : Z) (x : Σ i, X i) :
    (step.withRecord g).outcome (s, z) x =
      fTransform (fun p => ((p.1, g z x p.2), p.2)) (step.outcome s x) := by
  simp only [ProbStep.outcome, ProbStep.withRecord, Distribution.ProbDist.map,
    fTransform_fTransform]
  rfl

/-- **A record does not change the resource**: the probabilistic automaton with a record is the
same resource as the automaton. -/
lemma Interface.Resource.ofProbAutomaton_withRecord {T : Interface} {S Z : Type}
    (step : ProbStep S T.I T.X T.Y) (g : Z → (Σ i, T.X i) → (Σ i, T.Y i) → Z)
    (init : Distribution.ProbDist S) (z : Z) :
    Interface.Resource.ofProbAutomaton T (step.withRecord g)
        (Distribution.ProbDist.map (fun s => (s, z)) init) =
      Interface.Resource.ofProbAutomaton T step init := by
  refine Interface.Resource.ofProbAutomaton_eq_of_map _ _ _ _ Prod.fst (fun sz x => ?_) ?_
  · rw [ProbStep.outcome_withRecord, fTransform_fTransform]
    exact Finsupp.mapDomain_id.symm
  · rw [Distribution.ProbDist.map, fTransform_fTransform]
    exact Finsupp.mapDomain_id.symm

end SystemAlgebra

/-! ### Upstream candidates for `Common/AuthenticatedEncryption` -/

namespace Commons

open Probability Probability.Distribution SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface
open scoped SystemAlgebra

/-- **The law of the key** of a system that samples it at its first query: `Gen` before it, the
point law of the key after. -/
noncomputable def keyLaw {K : Type} (gen : Distribution.ProbDist K) : Option K → Distribution K
  | none => gen.1
  | some k => Finsupp.single k 1

section Encryption

variable {M C R : Type} [Fintype M] [Fintype C]

/-- The law of an encryption step, from its outcome. -/
lemma Encryption.val_eq_outcome
    (stepR : ProbStep R Encryption.Port (Encryption.Input M) (Encryption.Output C)) (r : R)
    (m : M) :
    (stepR r .enc m).1 =
      fTransform (fun p => (p.1, Encryption.ciphertextOf p.2)) (stepR.outcome r ⟨.enc, m⟩) := by
  rw [ProbStep.outcome, fTransform_fTransform]
  exact Finsupp.mapDomain_id.symm

end Encryption

variable {K M C T : Type} [Fintype K] [Fintype M] [Fintype C] [Fintype T] [DecidableEq K]
  [DecidableEq M]

/-- **`E_k` on fresh sampling**: the key is sampled at the first query, then `c ← Enc_k(m)`. -/
lemma Encryption.Real.step_enc (scheme : SymmetricEncryption K M C) (k : Option K) (m : M) :
    ((Encryption.Real.body scheme).probCombine
        (ProbStep.parallel (ProbStep.fresh (Encryption.Real.law1 scheme))
          (ProbStep.fresh (Encryption.Real.law2 scheme)))
        (Encryption.Real.bound_spec scheme) (k, ((), ())) .enc m).1 =
      bindK (keyLaw scheme.gen k) fun k' =>
        fTransform (fun c => ((some k', ((), ())), c)) (scheme.enc k' m).1 := by
  rw [Program.probCombine_val]
  cases k with
  | none =>
    rw [show Encryption.Real.bound scheme = 1 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩) (by simp [Encryption.Real.body, callProg]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def]
    refine bindK_congr fun z _ => ?_
    rw [Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
        (by simp [Encryption.Real.body, callProg, ProbStep.inlReply, ProbStep.tagged]),
      ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def]
    rw [fTransform_eq_bindK,
      ← bindK_pi_apply _ (fun km : K × M => (scheme.enc km.1 km.2).2.2) (z, m)]
    refine bindK_congr fun t _ => ?_
    rw [Program.probInvoke_inl (a := (some z, t (z, m)))
      (by simp [Encryption.Real.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply,
        ProbStep.tagged])]
  | some k =>
    rw [show Encryption.Real.bound scheme = 1 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩) (by simp [Encryption.Real.body, callProg]),
      ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, keyLaw, bindK_single, one_smul]
    rw [fTransform_eq_bindK,
      ← bindK_pi_apply _ (fun km : K × M => (scheme.enc km.1 km.2).2.2) (k, m)]
    refine bindK_congr fun t _ => ?_
    rw [Program.probInvoke_inl (a := (some k, t (k, m)))
      (by simp [Encryption.Real.body, callProg, returnProg, ProbStep.inrReply, ProbStep.tagged])]

/-- A possible step of `E_k`: the key is a possible key, and the ciphertext a possible encryption
under it. -/
lemma Encryption.Real.mem_support_step_enc (scheme : SymmetricEncryption K M C) (k : Option K)
    (m : M) {p : (Option K × (Unit × Unit)) × C}
    (hp : p ∈ ((Encryption.Real.body scheme).probCombine
        (ProbStep.parallel (ProbStep.fresh (Encryption.Real.law1 scheme))
          (ProbStep.fresh (Encryption.Real.law2 scheme)))
        (Encryption.Real.bound_spec scheme) (k, ((), ())) .enc m).1.support) :
    ∃ k' ∈ (keyLaw scheme.gen k).support, p = ((some k', ((), ())), p.2) ∧
      p.2 ∈ (scheme.enc k' m).1.support := by
  rw [Encryption.Real.step_enc] at hp
  obtain ⟨k', hk', hp'⟩ := mem_support_bindK hp
  obtain ⟨c, hc, rfl⟩ := mem_support_fTransform _ _ hp'
  exact ⟨k', hk', rfl, hc⟩

/-- **`⟦E_k, D_k⟧` on encryption**: the key is sampled at the first query, then
`c ← Enc_k(m)`. -/
lemma AE.Real.step_enc (scheme : SymmetricEncryption K M C) (k : Option K) (m : M) :
    ((AE.Real.body scheme).probCombine
        (ProbStep.parallel (ProbStep.fresh (AE.Real.law1 scheme))
          (ProbStep.fresh (AE.Real.law2 scheme)))
        (AE.Real.bound_spec scheme) (k, ((), ())) .enc m).1 =
      bindK (keyLaw scheme.gen k) fun k' =>
        fTransform (fun c => ((some k', ((), ())), c)) (scheme.enc k' m).1 := by
  rw [Program.probCombine_val]
  cases k with
  | none =>
    rw [show AE.Real.bound scheme = 1 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩) (by simp [AE.Real.body, callProg]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def]
    refine bindK_congr fun z _ => ?_
    rw [Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
        (by simp [AE.Real.body, callProg, ProbStep.inlReply, ProbStep.tagged]),
      ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def]
    rw [fTransform_eq_bindK,
      ← bindK_pi_apply _ (fun km : K × M => (scheme.enc km.1 km.2).2.2) (z, m)]
    refine bindK_congr fun t _ => ?_
    rw [Program.probInvoke_inl (a := (some z, t (z, m)))
      (by simp [AE.Real.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply,
        ProbStep.tagged])]
  | some k =>
    rw [show AE.Real.bound scheme = 1 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩) (by simp [AE.Real.body, callProg]),
      ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, keyLaw, bindK_single, one_smul]
    rw [fTransform_eq_bindK,
      ← bindK_pi_apply _ (fun km : K × M => (scheme.enc km.1 km.2).2.2) (k, m)]
    refine bindK_congr fun t _ => ?_
    rw [Program.probInvoke_inl (a := (some k, t (k, m)))
      (by simp [AE.Real.body, callProg, returnProg, ProbStep.inrReply, ProbStep.tagged])]

/-- **`⟦E_k, D_k⟧` on decryption**: the key is sampled at the first query, then `Dec_k(c)`. -/
lemma AE.Real.step_dec (scheme : SymmetricEncryption K M C) (k : Option K) (c : C) :
    ((AE.Real.body scheme).probCombine
        (ProbStep.parallel (ProbStep.fresh (AE.Real.law1 scheme))
          (ProbStep.fresh (AE.Real.law2 scheme)))
        (AE.Real.bound_spec scheme) (k, ((), ())) .dec c).1 =
      bindK (keyLaw scheme.gen k) fun k' =>
        Finsupp.single ((some k', ((), ())), scheme.dec k' c) 1 := by
  rw [Program.probCombine_val]
  cases k with
  | none =>
    rw [show AE.Real.bound scheme = 1 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩) (by simp [AE.Real.body, callProg]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def]
    refine bindK_congr fun z _ => ?_
    rw [Program.probInvoke_inl (a := (some z, scheme.dec z c))
      (by simp [AE.Real.body, callProg, returnProg, ProbStep.inlReply, ProbStep.tagged])]
  | some k =>
    rw [Program.probInvoke_inl (a := (some k, scheme.dec k c))
      (by simp [AE.Real.body, returnProg])]
    simp [keyLaw]

/-- **`⟦S_k, V_k⟧` on tagging**: the key is sampled at the first query, then `T ← S(k, m)`. -/
lemma MAC.Real.step_tag (mac : MAC K M T) (k : Option K) (m : M) :
    ((MAC.Real.body mac).probCombine
        (ProbStep.parallel (ProbStep.fresh (MAC.Real.law1 mac))
          (ProbStep.fresh (MAC.Real.law2 mac)))
        (MAC.Real.bound_spec mac) (k, ((), ())) .tag m).1 =
      bindK (keyLaw mac.gen k) fun k' =>
        fTransform (fun t => ((some k', ((), ())), t)) (mac.tag k' m).1 := by
  rw [Program.probCombine_val]
  cases k with
  | none =>
    rw [show MAC.Real.bound mac = 1 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩) (by simp [MAC.Real.body, callProg]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def]
    refine bindK_congr fun z _ => ?_
    rw [Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩)
        (by simp [MAC.Real.body, callProg, ProbStep.inlReply, ProbStep.tagged]),
      ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def]
    rw [fTransform_eq_bindK,
      ← bindK_pi_apply _ (fun km : K × M => (mac.tag km.1 km.2).2.2) (z, m)]
    refine bindK_congr fun t _ => ?_
    rw [Program.probInvoke_inl (a := (some z, t (z, m)))
      (by simp [MAC.Real.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply,
        ProbStep.tagged])]
  | some k =>
    rw [show MAC.Real.bound mac = 1 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inr (), ()⟩) (by simp [MAC.Real.body, callProg]),
      ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def, keyLaw, bindK_single, one_smul]
    rw [fTransform_eq_bindK,
      ← bindK_pi_apply _ (fun km : K × M => (mac.tag km.1 km.2).2.2) (k, m)]
    refine bindK_congr fun t _ => ?_
    rw [Program.probInvoke_inl (a := (some k, t (k, m)))
      (by simp [MAC.Real.body, callProg, returnProg, ProbStep.inrReply, ProbStep.tagged])]

/-- **`⟦S_k, V_k⟧` on verification**: the key is sampled at the first query, then
`V(k, m, T)`. -/
lemma MAC.Real.step_verify (mac : MAC K M T) (k : Option K) (m : M) (t : T) :
    ((MAC.Real.body mac).probCombine
        (ProbStep.parallel (ProbStep.fresh (MAC.Real.law1 mac))
          (ProbStep.fresh (MAC.Real.law2 mac)))
        (MAC.Real.bound_spec mac) (k, ((), ())) .verify (m, t)).1 =
      bindK (keyLaw mac.gen k) fun k' =>
        Finsupp.single ((some k', ((), ())), mac.verify k' m t) 1 := by
  rw [Program.probCombine_val]
  cases k with
  | none =>
    rw [show MAC.Real.bound mac = 1 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl (), ()⟩) (by simp [MAC.Real.body, callProg]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def]
    refine bindK_congr fun z _ => ?_
    rw [Program.probInvoke_inl (a := (some z, mac.verify z m t))
      (by simp [MAC.Real.body, callProg, returnProg, ProbStep.inlReply, ProbStep.tagged])]
  | some k =>
    rw [Program.probInvoke_inl (a := (some k, mac.verify k m t))
      (by simp [MAC.Real.body, returnProg])]
    simp [keyLaw]

section SUF

variable {R : Type} [DecidableEq T]

/-- **`mac-fake` on tagging**: tag through the inside step, of law `μ`, and record the pair. -/
lemma MAC.SUF.step_tag {stepR : ProbStep R Tagging.Port (Tagging.Input M T) (Tagging.Output T)}
    {s : Option (List (M × T))} {r : R} {m : M} {μ : Distribution (R × T)}
    (h : (stepR r .tag m).1 = μ) :
    ((MAC.SUF.body M T).probCombine stepR (MAC.SUF.bound_spec M T) (s, r) .tag m).1 =
      fTransform (fun rt => ((some (s.getD [] ++ [(m, rt.2)]), rt.1), rt.2)) μ := by
  subst h
  rw [Program.probCombine_val, show MAC.SUF.bound M T = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.tag, m⟩) (by cases s <;> simp [MAC.SUF.body, callProg])]
  simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
  rw [fTransform_eq_bindK]
  refine bindK_congr fun y _ => ?_
  rw [Program.probInvoke_inl (a := (some (s.getD [] ++ [(m, y.2)]), y.2))
    (by cases s <;> simp [MAC.SUF.body, callProg, returnProg, ProbStep.tagged])]
  rfl

/-- **`mac-fake` on verification**: verify through the inside step, of law `μ`, and accept only a
recorded pair. -/
lemma MAC.SUF.step_verify
    {stepR : ProbStep R Tagging.Port (Tagging.Input M T) (Tagging.Output T)}
    {s : Option (List (M × T))} {r : R} {m : M} {t : T} {μ : Distribution (R × Bool)}
    (h : (stepR r .verify (m, t)).1 = μ) :
    ((MAC.SUF.body M T).probCombine stepR (MAC.SUF.bound_spec M T) (s, r) .verify (m, t)).1 =
      fTransform (fun rv => ((some (s.getD []), rv.1), rv.2 && decide ((m, t) ∈ s.getD []))) μ := by
  subst h
  rw [Program.probCombine_val, show MAC.SUF.bound M T = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.verify, (m, t)⟩)
      (by cases s <;> simp [MAC.SUF.body, callProg])]
  simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
  rw [fTransform_eq_bindK]
  refine bindK_congr fun y _ => ?_
  rw [Program.probInvoke_inl (a := (some (s.getD []), y.2 && decide ((m, t) ∈ s.getD [])))
    (by cases s <;> simp [MAC.SUF.body, callProg, returnProg, ProbStep.tagged])]
  rfl

end SUF

/-- `⟦E_k, D_k⟧` as fresh sampling. -/
noncomputable def AE.Real.freshSampling (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ) :
    FreshSampling (AE.perPort M C q) (AE.Real.perPort scheme) :=
  ((FreshSampling.source (AE.Real.law1 scheme) _).parallel
    (FreshSampling.source (AE.Real.law2 scheme) _)).ofProgram none _ _ _

/-- `⟦S_k, V_k⟧` as fresh sampling. -/
noncomputable def MAC.Real.freshSampling (mac : MAC K M T) (q : Tagging.Port → ℕ) :
    FreshSampling (Tagging.perPort M T q) (MAC.Real.perPort mac) :=
  ((FreshSampling.source (MAC.Real.law1 mac) _).parallel
    (FreshSampling.source (MAC.Real.law2 mac) _)).ofProgram none _ _ _

/-- `mac-fake`, `⟦S_k, V_k⟧` accepting only the tagged pairs, as fresh sampling. -/
noncomputable def MAC.SUF.freshSamplingReal [DecidableEq T] (mac : MAC K M T)
    (q : Tagging.Port → ℕ) :
    FreshSampling (Tagging.perPort M T q) (MAC.SUF.perPort M T • MAC.Real.perPort mac) := by
  unfold MAC.SUF.perPort MAC.SUF.perPortProgram
  exact (MAC.Real.freshSampling mac q).ofPreservingProgram none _ _ _ _ _ _ _

/-- `ρ^ctxt(E_k)` as fresh sampling. -/
noncomputable def AE.CTXT.freshSamplingReal [DecidableEq C] (scheme : SymmetricEncryption K M C)
    (q : AE.Port → ℕ) :
    FreshSampling (AE.perPort M C q) (ρ^ctxt • Encryption.Real.perPort scheme) := by
  unfold AE.CTXT.perPort AE.CTXT.perPortProgram
  exact (Encryption.Real.freshSampling scheme (AE.CTXT.insideBudget M C q)).ofPreservingProgram
    none _ _ _ _ _ _ _

/-! ### Upstream candidates for `Common/Encryption` -/

section LeftRight

omit [DecidableEq M]

variable {R : Type}

/-- **`Left` on encryption**: encrypt the left message through the inside step, of law `μ`. -/
lemma Encryption.Left.step_enc
    {stepR : ProbStep R Encryption.Port (Encryption.Input M) (Encryption.Output C)}
    {s : Option Unit} {r : R} {mL mR : M} {μ : Distribution (R × C)}
    (h : (stepR r .enc mL).1 = μ) :
    ((Encryption.Left.body M C).probCombine stepR (Encryption.Left.bound_spec M C) (s, r) .enc
        (mL, mR)).1 = fTransform (fun rc => ((some (), rc.1), rc.2)) μ := by
  subst h
  rw [Program.probCombine_val, show Encryption.Left.bound M C = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.enc, mL⟩)
      (by cases s <;> simp [Encryption.Left.body, callProg])]
  simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
  rw [fTransform_eq_bindK]
  refine bindK_congr fun y _ => ?_
  rw [Program.probInvoke_inl (a := ((some (), y.2) : _ × LeftRight.Output C .enc))
    (by cases s <;> simp [Encryption.Left.body, callProg, returnProg, ProbStep.tagged])]
  rfl

/-- **`Right` on encryption**: encrypt the right message through the inside step, of law `μ`. -/
lemma Encryption.Right.step_enc
    {stepR : ProbStep R Encryption.Port (Encryption.Input M) (Encryption.Output C)}
    {s : Option Unit} {r : R} {mL mR : M} {μ : Distribution (R × C)}
    (h : (stepR r .enc mR).1 = μ) :
    ((Encryption.Right.body M C).probCombine stepR (Encryption.Right.bound_spec M C) (s, r) .enc
        (mL, mR)).1 = fTransform (fun rc => ((some (), rc.1), rc.2)) μ := by
  subst h
  rw [Program.probCombine_val, show Encryption.Right.bound M C = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.enc, mR⟩)
      (by cases s <;> simp [Encryption.Right.body, callProg])]
  simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
  rw [fTransform_eq_bindK]
  refine bindK_congr fun y _ => ?_
  rw [Program.probInvoke_inl (a := ((some (), y.2) : _ × LeftRight.Output C .enc))
    (by cases s <;> simp [Encryption.Right.body, callProg, returnProg, ProbStep.tagged])]
  rfl

variable [DecidableEq C] {stepR : ProbStep R AE.Port (AE.Input M C) (AE.Output M C)}
  {s : Option (List C)} {r : R}

/-- **`cca-left` on encryption**: encrypt the left message through the inside step, of law `μ`,
and record the ciphertext in `𝒟`. -/
lemma Encryption.LeftCCA.step_enc {mL mR : M} {μ : Distribution (R × C)}
    (h : (stepR r .enc mL).1 = μ) :
    ((Encryption.LeftCCA.body M C).probCombine stepR (Encryption.LeftCCA.bound_spec M C) (s, r)
        .enc (mL, mR)).1 = fTransform (fun rc => ((some (s.getD [] ++ [rc.2]), rc.1), rc.2)) μ := by
  subst h
  rw [Program.probCombine_val, show Encryption.LeftCCA.bound M C = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.enc, mL⟩)
      (by cases s <;> simp [Encryption.LeftCCA.body, callProg])]
  simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
  rw [fTransform_eq_bindK]
  refine bindK_congr fun y _ => ?_
  rw [Program.probInvoke_inl
    (a := ((some (s.getD [] ++ [y.2]), y.2) : _ × LeftRightCCA.Output M C .enc))
    (by cases s <;> simp [Encryption.LeftCCA.body, callProg, returnProg, ProbStep.tagged])]
  rfl

/-- **`cca-right` on encryption**: encrypt the right message through the inside step, of law
`μ`, and record the ciphertext in `𝒟`. -/
lemma Encryption.RightCCA.step_enc {mL mR : M} {μ : Distribution (R × C)}
    (h : (stepR r .enc mR).1 = μ) :
    ((Encryption.RightCCA.body M C).probCombine stepR (Encryption.RightCCA.bound_spec M C) (s, r)
        .enc (mL, mR)).1 = fTransform (fun rc => ((some (s.getD [] ++ [rc.2]), rc.1), rc.2)) μ := by
  subst h
  rw [Program.probCombine_val, show Encryption.RightCCA.bound M C = 0 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.enc, mR⟩)
      (by cases s <;> simp [Encryption.RightCCA.body, callProg])]
  simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
  rw [fTransform_eq_bindK]
  refine bindK_congr fun y _ => ?_
  rw [Program.probInvoke_inl
    (a := ((some (s.getD [] ++ [y.2]), y.2) : _ × LeftRightCCA.Output M C .enc))
    (by cases s <;> simp [Encryption.RightCCA.body, callProg, returnProg, ProbStep.tagged])]
  rfl

/-- **`cca-left` on decryption**: `⊥` on a ciphertext of `𝒟`, otherwise decrypt through the
inside step, of law `μ`. -/
lemma Encryption.LeftCCA.step_dec {c : C} {μ : Distribution (R × Option M)}
    (h : (stepR r .dec c).1 = μ) :
    ((Encryption.LeftCCA.body M C).probCombine stepR (Encryption.LeftCCA.bound_spec M C) (s, r)
        .dec c).1 =
      if c ∈ s.getD [] then Finsupp.single ((some (s.getD []), r), none) 1
      else fTransform (fun rm => ((some (s.getD []), rm.1), rm.2)) μ := by
  subst h
  rw [Program.probCombine_val]
  by_cases hc : c ∈ s.getD []
  · rw [if_pos hc, Program.probInvoke_inl (a := (some (s.getD []), none))
      (by cases s <;> simp_all [Encryption.LeftCCA.body, returnProg])]
  · rw [if_neg hc, show Encryption.LeftCCA.bound M C = 0 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.dec, c⟩)
        (by cases s <;> simp_all [Encryption.LeftCCA.body, callProg])]
    simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
    rw [fTransform_eq_bindK]
    refine bindK_congr fun y _ => ?_
    rw [Program.probInvoke_inl
      (a := ((some (s.getD []), y.2) : _ × LeftRightCCA.Output M C .dec))
      (by cases s <;> simp_all [Encryption.LeftCCA.body, callProg, returnProg, ProbStep.tagged])]
    rfl

/-- **`cca-right` on decryption**: `⊥` on a ciphertext of `𝒟`, otherwise decrypt through the
inside step, of law `μ`. -/
lemma Encryption.RightCCA.step_dec {c : C} {μ : Distribution (R × Option M)}
    (h : (stepR r .dec c).1 = μ) :
    ((Encryption.RightCCA.body M C).probCombine stepR (Encryption.RightCCA.bound_spec M C) (s, r)
        .dec c).1 =
      if c ∈ s.getD [] then Finsupp.single ((some (s.getD []), r), none) 1
      else fTransform (fun rm => ((some (s.getD []), rm.1), rm.2)) μ := by
  subst h
  rw [Program.probCombine_val]
  by_cases hc : c ∈ s.getD []
  · rw [if_pos hc, Program.probInvoke_inl (a := (some (s.getD []), none))
      (by cases s <;> simp_all [Encryption.RightCCA.body, returnProg])]
  · rw [if_neg hc, show Encryption.RightCCA.bound M C = 0 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.dec, c⟩)
        (by cases s <;> simp_all [Encryption.RightCCA.body, callProg])]
    simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
    rw [fTransform_eq_bindK]
    refine bindK_congr fun y _ => ?_
    rw [Program.probInvoke_inl
      (a := ((some (s.getD []), y.2) : _ × LeftRightCCA.Output M C .dec))
      (by cases s <;> simp_all [Encryption.RightCCA.body, callProg, returnProg, ProbStep.tagged])]
    rfl

end LeftRight

/-- `cpa-left`, `Left` on `E_k`, as fresh sampling. -/
noncomputable def Encryption.Left.freshSamplingReal (scheme : SymmetricEncryption K M C)
    (q : LeftRight.Port → ℕ) :
    FreshSampling (LeftRight.perPort M C q)
      (Encryption.Left.perPort M C • Encryption.Real.perPort scheme) := by
  unfold Encryption.Left.perPort Encryption.Left.perPortProgram
  exact (Encryption.Real.freshSampling scheme _).ofPreservingProgram none _ _ _ _ _ _ _

/-- `cpa-right`, `Right` on `E_k`, as fresh sampling. -/
noncomputable def Encryption.Right.freshSamplingReal (scheme : SymmetricEncryption K M C)
    (q : LeftRight.Port → ℕ) :
    FreshSampling (LeftRight.perPort M C q)
      (Encryption.Right.perPort M C • Encryption.Real.perPort scheme) := by
  unfold Encryption.Right.perPort Encryption.Right.perPortProgram
  exact (Encryption.Real.freshSampling scheme _).ofPreservingProgram none _ _ _ _ _ _ _

/-- `cca-left`, the transformation of `⟦E_k, D_k⟧`, as fresh sampling. -/
noncomputable def Encryption.LeftCCA.freshSamplingReal [DecidableEq C]
    (scheme : SymmetricEncryption K M C) (q : LeftRightCCA.Port → ℕ) :
    FreshSampling (LeftRightCCA.perPort M C q)
      (Encryption.LeftCCA.perPort M C • AE.Real.perPort scheme) := by
  unfold Encryption.LeftCCA.perPort Encryption.LeftCCA.perPortProgram
  exact (AE.Real.freshSampling scheme _).ofPreservingProgram none _ _ _ _ _ _ _

/-- `cca-right`, the transformation of `⟦E_k, D_k⟧`, as fresh sampling. -/
noncomputable def Encryption.RightCCA.freshSamplingReal [DecidableEq C]
    (scheme : SymmetricEncryption K M C) (q : LeftRightCCA.Port → ℕ) :
    FreshSampling (LeftRightCCA.perPort M C q)
      (Encryption.RightCCA.perPort M C • AE.Real.perPort scheme) := by
  unfold Encryption.RightCCA.perPort Encryption.RightCCA.perPortProgram
  exact (AE.Real.freshSampling scheme _).ofPreservingProgram none _ _ _ _ _ _ _

end Commons

namespace ProofLadders.EtM

open Commons Probability SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface
open CategoryTheory ConstructiveCryptography.CryptographicAlgebra
open scoped SystemAlgebra SystemAlgebra.DSL

noncomputable section

variable {Ke Km M C T : Type} [Fintype Ke] [Fintype Km] [Fintype M] [Fintype C] [Fintype T]

/-- **Encrypt-then-MAC** [4, §5]: `Enc(k_e ‖ k_m, m) = (c', Mac(k_m, c'))` for
`c' ← Σ_e.Enc(k_e, m)`, and `Dec(k_e ‖ k_m, (c', T))` decrypts `c'` if `Ver(k_m, c', T)`, and is
`⊥` otherwise. -/
def EncryptThenMAC [DecidableEq C] (scheme : SymmetricEncryption Ke M C) (mac : MAC Km C T) :
    SymmetricEncryption (Ke × Km) M (C × T) where
  gen := Distribution.prodProbDist scheme.gen mac.gen
  enc k m := Distribution.ProbDist.bind (scheme.enc k.1 m) fun c =>
    Distribution.ProbDist.map (fun t => (c, t)) (mac.tag k.2 c)
  dec k c := if mac.verify k.2 c.1 c.2 then scheme.dec k.1 c.1 else none

-- `π_EtM`: on `m`, `c' ← encryption.enc(m)` and `T ← tagging.tag(c')`, return `(c', T)`; on
-- `(c', T)`, `encryption.dec(c')` if `tagging.verify(c', T)`, otherwise `⊥`.
converter 𝓟(M C T : Type) [Fintype M] [Fintype C] [Fintype T] : AE M (C × T)
  inside encryption : AE M C
  inside tagging : Tagging C T
  on enc(message : M) → C × T
    c ← encryption.enc(message)
    t ← tagging.tag(c)
    return (c, t)
  on dec(ciphertext : C × T) → Option M
    valid ← tagging.verify(ciphertext.1, ciphertext.2)
    if valid
      m ← encryption.dec(ciphertext.1)
      return m
    else
      return none

-- `π_enc`: on `m`, `c' ← encryption.enc(m)` and `T ← tagging.tag(c')`, return `(c', T)`.
converter 𝓟ₑ(M C T : Type) [Fintype M] [Fintype C] [Fintype T] : Encryption M (C × T)
  inside encryption : Encryption M C
  inside tagging : Tagging C T
  on enc(message : M) → C × T
    c ← encryption.enc(message)
    t ← tagging.tag(c)
    return (c, t)

/-- The inside calls of `π_EtM` per procedure: encryption and tagging for `enc`, verification
and decryption for `dec`. -/
def 𝓟.calls : AE.Port → AE.Port ⊕ Tagging.Port → ℕ
  | .enc, .inl .enc => 1
  | .enc, .inr .tag => 1
  | .dec, .inl .dec => 1
  | .dec, .inr .verify => 1
  | _, _ => 0

/-- `π_EtM` calls each inside label at most `𝓟.calls` times per procedure. -/
lemma 𝓟.labelBounded : (𝓟.body M C T).LabelBounded 𝓟.calls := by
  intro s o u
  cases o <;> simp only [𝓟.body] <;> cases s <;> dsimp only <;>
    repeat' (first
      | exact Program.labelCallBound_return _ _
      | (refine Program.labelCallBound_call _ _ _ (by decide) fun y => ?_)
      | split)

/-- The tagging budget of `π_EtM`: a tag per encryption, a verification per decryption. -/
abbrev tagBudget (q : AE.Port → ℕ) : Tagging.Port → ℕ
  | .tag => q .enc
  | .verify => q .dec

/-- The inside interface of `π_EtM`: the encryption scheme beside the MAC. -/
abbrev 𝓟.inside (M C T : Type) [Fintype M] [Fintype C] [Fintype T] (q : AE.Port → ℕ) :
    Interface :=
  (AE.perPort M C q).tensor (Tagging.perPort C T (tagBudget q))

lemma 𝓟.admits (q : AE.Port → ℕ) :
    (𝓟.inside M C T q).AdmitsLabelBudget fun j => ∑ o, 𝓟.calls o j * q o := by
  refine ((portBudget_admitsLabelBudget _ _ _ _).tensor
    (portBudget_admitsLabelBudget _ _ _ _)).mono fun j => ?_
  rcases j with (_ | _) | (_ | _) <;> simp [Finset.univ, Fintype.elems, 𝓟.calls, tagBudget]

/-- **`π_EtM` at per-port budgets**: `q_e` encryptions and tags, `q_d` verifications and
decryptions. -/
def 𝓟.perLabel (q : AE.Port → ℕ) : AE.perPort M (C × T) q ⟶ 𝓟.inside M C T q :=
  Converter.ofLabelBoundedProgram (A := AE.perPort M (C × T) q) (B := 𝓟.inside M C T q) none
    (𝓟.body M C T) (𝓟.bound_spec M C T) 𝓟.calls 𝓟.labelBounded q (fun _ hd => hd.2)
    (𝓟.admits q)

/-- The inside calls of `π_enc` per procedure: encryption and tagging. -/
def 𝓟ₑ.calls : Encryption.Port → Encryption.Port ⊕ Tagging.Port → ℕ
  | .enc, .inl .enc => 1
  | .enc, .inr .tag => 1
  | _, _ => 0

lemma 𝓟ₑ.labelBounded : (𝓟ₑ.body M C T).LabelBounded 𝓟ₑ.calls := by
  intro s o u
  cases o
  simp only [𝓟ₑ.body]
  cases s <;> dsimp only <;>
    repeat' (first
      | exact Program.labelCallBound_return _ _
      | (refine Program.labelCallBound_call _ _ _ (by decide) fun y => ?_))

/-- The tagging budget of `π_enc`: a tag per encryption, no verification. -/
abbrev encTagBudget (q : Encryption.Port → ℕ) : Tagging.Port → ℕ
  | .tag => q .enc
  | .verify => 0

/-- The inside interface of `π_enc`. -/
abbrev 𝓟ₑ.inside (M C T : Type) [Fintype M] [Fintype C] [Fintype T]
    (q : Encryption.Port → ℕ) : Interface :=
  (Encryption.perPort M C q).tensor (Tagging.perPort C T (encTagBudget q))

lemma 𝓟ₑ.admits (q : Encryption.Port → ℕ) :
    (𝓟ₑ.inside M C T q).AdmitsLabelBudget fun j => ∑ o, 𝓟ₑ.calls o j * q o := by
  refine ((portBudget_admitsLabelBudget _ _ _ _).tensor
    (portBudget_admitsLabelBudget _ _ _ _)).mono fun j => ?_
  rcases j with _ | (_ | _) <;> simp [Finset.univ, Fintype.elems, 𝓟ₑ.calls, encTagBudget]

/-- **`π_enc` at per-port budgets.** -/
def 𝓟ₑ.perLabel (q : Encryption.Port → ℕ) :
    Encryption.perPort M (C × T) q ⟶ 𝓟ₑ.inside M C T q :=
  Converter.ofLabelBoundedProgram (A := Encryption.perPort M (C × T) q)
    (B := 𝓟ₑ.inside M C T q) none (𝓟ₑ.body M C T) (𝓟ₑ.bound_spec M C T)
    𝓟ₑ.calls 𝓟ₑ.labelBounded q (fun _ hd => hd.2) (𝓟ₑ.admits q)

-- `𝓜 b`: `k_e ← G_e`; on `(m_L, m_R)`, `c' ← Enc(k_e, m_b)`, `T ← tagging.tag(c')`, and add
-- `(c', T)` to `𝒟`; on `c`, `⊥` if `c ∈ 𝒟`, otherwise `Dec(k_e, c')` if
-- `tagging.verify(c', T)` and `⊥` if not.
converter 𝓜(T : Type) [Fintype T] [DecidableEq C] [DecidableEq T] (scheme : SymmetricEncryption Ke M C) [DecidableEq Ke] [DecidableEq M] (b : Bool) : LeftRightCCA M (C × T)
  inside tagging : Tagging C T
  initialize
    ke ←$ scheme.gen
    challenges ← ([] : List (C × T))
  on enc(left : M, right : M) → C × T
    encryptions ←$ scheme.encryptions
    c' ← encryptions (ke, if b then right else left)
    t ← tagging.tag(c')
    challenges ← challenges ++ [(c', t)]
    return (c', t)
  on dec(ciphertext : C × T) → Option M
    if decide (ciphertext ∈ challenges)
      return none
    else
      valid ← tagging.verify(ciphertext.1, ciphertext.2)
      if valid
        return scheme.dec ke ciphertext.1
      else
        return none

-- `𝓒`: `k_m ← G_m`; on `(m_L, m_R)`, `c' ← cpa.enc(m_L, m_R)` and return
-- `(c', Mac(k_m, c'))`; on `c`, `⊥`.
converter 𝓒(M C : Type) [Fintype M] [Fintype C] [DecidableEq C] (mac : MAC Km C T) [DecidableEq Km] : LeftRightCCA M (C × T)
  inside cpa : LeftRight M C
  initialize
    km ←$ mac.gen
  on enc(left : M, right : M) → C × T
    c' ← cpa.enc(left, right)
    tags ←$ mac.tags
    return (c', tags (km, c'))
  on dec(_ciphertext : C × T) → Option M
    return none

/-! ### `π_EtM` and `π_enc` as steps -/

section Steps

open Probability.Distribution

variable {RE RT : Type} {stepT : ProbStep RT Tagging.Port (Tagging.Input C T) (Tagging.Output T)}
  {s : Option Unit} {r : RT}

/-- **`π_enc` on encryption**: `c' ← encryption.enc(m)`, then `T ← tagging.tag(c')`, on the laws
`μE` and `μT` of the inside steps. -/
lemma 𝓟ₑ.step_enc
    {stepE : ProbStep RE Encryption.Port (Encryption.Input M) (Encryption.Output C)} {e : RE}
    {m : M} {μE : Distribution (RE × C)} {μT : C → Distribution (RT × T)}
    (hE : (stepE e .enc m).1 = μE) (hT : ∀ c, (stepT r .tag c).1 = μT c) :
    ((𝓟ₑ.body M C T).probCombine (ProbStep.parallel stepE stepT) (𝓟ₑ.bound_spec M C T)
        (s, (e, r)) .enc m).1 =
      bindK μE fun ec =>
        fTransform (fun rt => ((some (), (ec.1, rt.1)), (ec.2, rt.2))) (μT ec.2) := by
  subst hE
  obtain rfl : μT = fun c => (stepT r .tag c).1 := funext fun c => (hT c).symm
  rw [Program.probCombine_val, show 𝓟ₑ.bound M C T = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl .enc, m⟩) (by cases s <;> simp [𝓟ₑ.body, callProg]),
    ProbStep.outcome_parallel_inl]
  simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
  refine bindK_congr fun y _ => ?_
  rw [Program.probInvoke_succ_inr (q := ⟨.inr .tag, y.2⟩)
      (by cases s <;> simp [𝓟ₑ.body, callProg, ProbStep.inlReply, ProbStep.tagged]),
    ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
  rw [fTransform_eq_bindK]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_inl (a := (some (), (y.2, z.2)))
    (by cases s <;> simp [𝓟ₑ.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply,
      ProbStep.tagged])]
  rfl

variable {stepA : ProbStep RE AE.Port (AE.Input M C) (AE.Output M C)} {a : RE}

/-- **`π_EtM` on encryption**: `c' ← encryption.enc(m)`, then `T ← tagging.tag(c')`, on the laws
`μA` and `μT` of the inside steps. -/
lemma 𝓟.step_enc {m : M} {μA : Distribution (RE × C)} {μT : C → Distribution (RT × T)}
    (hA : (stepA a .enc m).1 = μA) (hT : ∀ c, (stepT r .tag c).1 = μT c) :
    ((𝓟.body M C T).probCombine (ProbStep.parallel stepA stepT) (𝓟.bound_spec M C T)
        (s, (a, r)) .enc m).1 =
      bindK μA fun ac =>
        fTransform (fun rt => ((some (), (ac.1, rt.1)), (ac.2, rt.2))) (μT ac.2) := by
  subst hA
  obtain rfl : μT = fun c => (stepT r .tag c).1 := funext fun c => (hT c).symm
  rw [Program.probCombine_val, show 𝓟.bound M C T = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inl .enc, m⟩) (by cases s <;> simp [𝓟.body, callProg]),
    ProbStep.outcome_parallel_inl]
  simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
  refine bindK_congr fun y _ => ?_
  rw [Program.probInvoke_succ_inr (q := ⟨.inr .tag, y.2⟩)
      (by cases s <;> simp [𝓟.body, callProg, ProbStep.inlReply, ProbStep.tagged]),
    ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
  rw [fTransform_eq_bindK]
  refine bindK_congr fun z _ => ?_
  rw [Program.probInvoke_inl (a := (some (), (y.2, z.2)))
    (by cases s <;> simp [𝓟.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply,
      ProbStep.tagged])]
  rfl

/-- **`π_EtM` on decryption**: `tagging.verify(c', T)`, then `encryption.dec(c')` if it holds and
`⊥` otherwise, on the laws `μT` and `μA` of the inside steps. -/
lemma 𝓟.step_dec {c : C} {t : T} {μA : Distribution (RE × Option M)}
    {μT : Distribution (RT × Bool)} (hA : (stepA a .dec c).1 = μA)
    (hT : (stepT r .verify (c, t)).1 = μT) :
    ((𝓟.body M C T).probCombine (ProbStep.parallel stepA stepT) (𝓟.bound_spec M C T)
        (s, (a, r)) .dec (c, t)).1 =
      bindK μT fun rv =>
        if rv.2 then fTransform (fun am => ((some (), (am.1, rv.1)), am.2)) μA
        else Finsupp.single ((some (), (a, rv.1)), none) 1 := by
  subst hA hT
  rw [Program.probCombine_val, show 𝓟.bound M C T = 1 + 1 from rfl,
    Program.probInvoke_succ_inr (q := ⟨.inr .verify, (c, t)⟩)
      (by cases s <;> simp [𝓟.body, callProg]),
    ProbStep.outcome_parallel_inr]
  simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
  refine bindK_congr fun y _ => ?_
  obtain ⟨r', v⟩ := y
  cases v with
  | true =>
    rw [Program.probInvoke_succ_inr (q := ⟨.inl .dec, c⟩)
        (by cases s <;> simp [𝓟.body, callProg, ProbStep.inrReply, ProbStep.tagged]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def, if_true]
    rw [fTransform_eq_bindK]
    refine bindK_congr fun z _ => ?_
    rw [Program.probInvoke_inl (a := ((some (), z.2) : Option Unit × Option M))
      (by cases s <;> simp [𝓟.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply,
        ProbStep.tagged])]
    rfl
  | false =>
    rw [Program.probInvoke_inl (a := (some (), none))
      (by cases s <;> simp [𝓟.body, callProg, returnProg, ProbStep.inrReply, ProbStep.tagged])]
    rfl

end Steps

variable [DecidableEq Ke] [DecidableEq Km] [DecidableEq M] [DecidableEq C] [DecidableEq T]

/-! ### `𝓜 b` and `𝓒` as steps -/

section CallingPrograms

open Probability.Distribution

variable {RT : Type} {stepT : ProbStep RT Tagging.Port (Tagging.Input C T) (Tagging.Output T)}
  {r : RT}

omit [DecidableEq Km] in
/-- **`𝓜 b` on encryption**: `k_e` is sampled at the first query, then `c' ← Enc(k_e, m_b)`,
`T ← tagging.tag(c')`, and `(c', T)` is added to `𝒟`, on the law `μT` of the inside step. -/
lemma 𝓜.step_enc (scheme : SymmetricEncryption Ke M C) (b : Bool)
    {s : Option (Ke × List (C × T))} {mL mR : M} {μT : C → Distribution (RT × T)}
    (hT : ∀ c, (stepT r .tag c).1 = μT c) :
    ((𝓜.body T scheme b).probCombine
        (ProbStep.parallel stepT (ProbStep.parallel (ProbStep.fresh (𝓜.law1 T scheme b))
          (ProbStep.fresh (𝓜.law2 T scheme b)))) (𝓜.bound_spec T scheme b)
        (s, (r, ((), ()))) .enc (mL, mR)).1 =
      bindK (keyLaw scheme.gen (s.map Prod.fst)) fun ke =>
        bindK (scheme.enc ke (if b then mR else mL)).1 fun c =>
          fTransform (fun rt => ((some (ke, (s.map Prod.snd).getD [] ++ [(c, rt.2)]),
            (rt.1, ((), ()))), (c, rt.2))) (μT c) := by
  obtain rfl : μT = fun c => (stepT r .tag c).1 := funext fun c => (hT c).symm
  rw [Program.probCombine_val]
  cases s with
  | none =>
    simp only [Option.map_none, Option.getD_none, keyLaw]
    rw [show 𝓜.bound T scheme b = 2 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inr (.inl ()), ()⟩) (by simp [𝓜.body, callProg]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def]
    refine bindK_congr fun ke _ => ?_
    rw [Program.probInvoke_succ_inr (q := ⟨.inr (.inr ()), ()⟩)
        (by simp [𝓜.body, callProg, ProbStep.inlReply, ProbStep.inrReply, ProbStep.tagged]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def]
    rw [← bindK_pi_apply _ (fun km : Ke × M => (scheme.enc km.1 km.2).2.2)
      (ke, if b then mR else mL)]
    refine bindK_congr fun E _ => ?_
    rw [Program.probInvoke_succ_inr (q := ⟨.inl .tag, E (ke, if b then mR else mL)⟩)
        (by simp [𝓜.body, callProg, ProbStep.inlReply, ProbStep.inrReply, ProbStep.tagged]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
    rw [fTransform_eq_bindK]
    refine bindK_congr fun y _ => ?_
    rw [Program.probInvoke_inl (a := ((some (ke, [] ++ [(E (ke, if b then mR else mL), y.2)]),
        (E (ke, if b then mR else mL), y.2)) : _ × LeftRightCCA.Output M (C × T) .enc))
      (by simp [𝓜.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply,
        ProbStep.tagged])]
    rfl
  | some p =>
    obtain ⟨ke, D⟩ := p
    simp only [Option.map_some, Option.getD_some, keyLaw, bindK_single, one_smul]
    rw [show 𝓜.bound T scheme b = 2 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inr (.inr ()), ()⟩) (by simp [𝓜.body, callProg]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def]
    rw [← bindK_pi_apply _ (fun km : Ke × M => (scheme.enc km.1 km.2).2.2)
      (ke, if b then mR else mL)]
    refine bindK_congr fun E _ => ?_
    rw [Program.probInvoke_succ_inr (q := ⟨.inl .tag, E (ke, if b then mR else mL)⟩)
        (by simp [𝓜.body, callProg, ProbStep.inrReply, ProbStep.tagged]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
    rw [fTransform_eq_bindK]
    refine bindK_congr fun y _ => ?_
    rw [Program.probInvoke_inl (a := ((some (ke, D ++ [(E (ke, if b then mR else mL), y.2)]),
        (E (ke, if b then mR else mL), y.2)) : _ × LeftRightCCA.Output M (C × T) .enc))
      (by simp [𝓜.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply,
        ProbStep.tagged])]
    rfl

omit [DecidableEq Km] in
/-- **`𝓜 b` on decryption**: `k_e` is sampled at the first query; then `⊥` on a ciphertext of
`𝒟`, and otherwise `Dec(k_e, c')` if `tagging.verify(c', T)` and `⊥` if not, on the law `μV` of
the inside step. -/
lemma 𝓜.step_dec (scheme : SymmetricEncryption Ke M C) (b : Bool)
    {s : Option (Ke × List (C × T))} {c : C} {t : T} {μV : Distribution (RT × Bool)}
    (hV : (stepT r .verify (c, t)).1 = μV) :
    ((𝓜.body T scheme b).probCombine
        (ProbStep.parallel stepT (ProbStep.parallel (ProbStep.fresh (𝓜.law1 T scheme b))
          (ProbStep.fresh (𝓜.law2 T scheme b)))) (𝓜.bound_spec T scheme b)
        (s, (r, ((), ()))) .dec (c, t)).1 =
      bindK (keyLaw scheme.gen (s.map Prod.fst)) fun ke =>
        if (c, t) ∈ (s.map Prod.snd).getD [] then
          Finsupp.single ((some (ke, (s.map Prod.snd).getD []), (r, ((), ()))), none) 1
        else bindK μV fun rv =>
          Finsupp.single ((some (ke, (s.map Prod.snd).getD []), (rv.1, ((), ()))),
            if rv.2 then scheme.dec ke c else none) 1 := by
  subst hV
  rw [Program.probCombine_val]
  cases s with
  | none =>
    simp only [Option.map_none, Option.getD_none, keyLaw, List.not_mem_nil, ↓reduceIte]
    rw [show 𝓜.bound T scheme b = 2 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inr (.inl ()), ()⟩) (by simp [𝓜.body, callProg]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def]
    refine bindK_congr fun ke _ => ?_
    rw [Program.probInvoke_succ_inr (q := ⟨.inl .verify, (c, t)⟩)
        (by simp [𝓜.body, callProg, ProbStep.inlReply, ProbStep.inrReply, ProbStep.tagged]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
    refine bindK_congr fun y _ => ?_
    obtain ⟨r', v⟩ := y
    cases v
    · rw [Program.probInvoke_inl
        (a := ((some (ke, []), none) : _ × LeftRightCCA.Output M (C × T) .dec))
        (by simp [𝓜.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply,
          ProbStep.tagged])]
      rfl
    · rw [Program.probInvoke_inl
        (a := ((some (ke, []), scheme.dec ke c) : _ × LeftRightCCA.Output M (C × T) .dec))
        (by simp [𝓜.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply,
          ProbStep.tagged])]
      rfl
  | some p =>
    obtain ⟨ke, D⟩ := p
    simp only [Option.map_some, Option.getD_some, keyLaw, bindK_single, one_smul]
    by_cases hc : (c, t) ∈ D
    · rw [if_pos hc, Program.probInvoke_inl
        (a := ((some (ke, D), none) : _ × LeftRightCCA.Output M (C × T) .dec))
        (by simp [𝓜.body, returnProg, hc])]
    · rw [if_neg hc, show 𝓜.bound T scheme b = 2 + 1 from rfl,
        Program.probInvoke_succ_inr (q := ⟨.inl .verify, (c, t)⟩)
          (by simp [𝓜.body, callProg, hc]),
        ProbStep.outcome_parallel_inl]
      simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
      refine bindK_congr fun y _ => ?_
      obtain ⟨r', v⟩ := y
      cases v
      · rw [Program.probInvoke_inl
          (a := ((some (ke, D), none) : _ × LeftRightCCA.Output M (C × T) .dec))
          (by simp [𝓜.body, callProg, returnProg, ProbStep.inlReply, ProbStep.tagged, hc])]
        rfl
      · rw [Program.probInvoke_inl
          (a := ((some (ke, D), scheme.dec ke c) : _ × LeftRightCCA.Output M (C × T) .dec))
          (by simp [𝓜.body, callProg, returnProg, ProbStep.inlReply, ProbStep.tagged, hc])]
        rfl

variable {RC : Type}
  {stepC : ProbStep RC LeftRight.Port (LeftRight.Input M) (LeftRight.Output C)} {r : RC}

omit [DecidableEq Ke] [DecidableEq M] [DecidableEq T] in
/-- **`𝓒` on encryption**: `k_m` is sampled at the first query, then `c' ← cpa.enc(m_L, m_R)`
and `T ← Mac(k_m, c')`, on the law `μC` of the inside step. -/
lemma 𝓒.step_enc (mac : MAC Km C T) {s : Option Km} {mL mR : M} {μC : Distribution (RC × C)}
    (hC : (stepC r .enc (mL, mR)).1 = μC) :
    ((𝓒.body M C mac).probCombine
        (ProbStep.parallel stepC (ProbStep.parallel (ProbStep.fresh (𝓒.law1 M C mac))
          (ProbStep.fresh (𝓒.law2 M C mac)))) (𝓒.bound_spec M C mac)
        (s, (r, ((), ()))) .enc (mL, mR)).1 =
      bindK (keyLaw mac.gen s) fun km => bindK μC fun rc =>
        fTransform (fun t => ((some km, (rc.1, ((), ()))), (rc.2, t))) (mac.tag km rc.2).1 := by
  subst hC
  rw [Program.probCombine_val]
  cases s with
  | none =>
    rw [show 𝓒.bound M C mac = 2 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inr (.inl ()), ()⟩) (by simp [𝓒.body, callProg]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def]
    refine bindK_congr fun km _ => ?_
    rw [Program.probInvoke_succ_inr (q := ⟨.inl .enc, (mL, mR)⟩)
        (by simp [𝓒.body, callProg, ProbStep.inlReply, ProbStep.inrReply, ProbStep.tagged]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def]
    refine bindK_congr fun y _ => ?_
    rw [Program.probInvoke_succ_inr (q := ⟨.inr (.inr ()), ()⟩)
        (by simp [𝓒.body, callProg, ProbStep.inlReply, ProbStep.inrReply, ProbStep.tagged]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def]
    rw [fTransform_eq_bindK,
      ← bindK_pi_apply _ (fun kc : Km × C => (mac.tag kc.1 kc.2).2.2) (km, y.2)]
    refine bindK_congr fun tags _ => ?_
    rw [Program.probInvoke_inl
      (a := ((some km, (y.2, tags (km, y.2))) : _ × LeftRightCCA.Output M (C × T) .enc))
      (by simp [𝓒.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply,
        ProbStep.tagged])]
    rfl
  | some km =>
    rw [show 𝓒.bound M C mac = 2 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inl .enc, (mL, mR)⟩) (by simp [𝓒.body, callProg]),
      ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, bindK_fTransform, Function.comp_def, keyLaw, bindK_single,
      one_smul]
    refine bindK_congr fun y _ => ?_
    rw [Program.probInvoke_succ_inr (q := ⟨.inr (.inr ()), ()⟩)
        (by simp [𝓒.body, callProg, ProbStep.inlReply, ProbStep.tagged]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inr]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def]
    rw [fTransform_eq_bindK,
      ← bindK_pi_apply _ (fun kc : Km × C => (mac.tag kc.1 kc.2).2.2) (km, y.2)]
    refine bindK_congr fun tags _ => ?_
    rw [Program.probInvoke_inl
      (a := ((some km, (y.2, tags (km, y.2))) : _ × LeftRightCCA.Output M (C × T) .enc))
      (by simp [𝓒.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply,
        ProbStep.tagged])]
    rfl

omit [DecidableEq Ke] [DecidableEq M] [DecidableEq T] in
/-- **`𝓒` on decryption**: `k_m` is sampled at the first query, and the reply is `⊥`. -/
lemma 𝓒.step_dec (mac : MAC Km C T) {s : Option Km} (c : C × T) :
    ((𝓒.body M C mac).probCombine
        (ProbStep.parallel stepC (ProbStep.parallel (ProbStep.fresh (𝓒.law1 M C mac))
          (ProbStep.fresh (𝓒.law2 M C mac)))) (𝓒.bound_spec M C mac)
        (s, (r, ((), ()))) .dec c).1 =
      bindK (keyLaw mac.gen s) fun km => Finsupp.single ((some km, (r, ((), ()))), none) 1 := by
  rw [Program.probCombine_val]
  cases s with
  | none =>
    rw [show 𝓒.bound M C mac = 2 + 1 from rfl,
      Program.probInvoke_succ_inr (q := ⟨.inr (.inl ()), ()⟩) (by simp [𝓒.body, callProg]),
      ProbStep.outcome_parallel_inr, ProbStep.outcome_parallel_inl]
    simp only [ProbStep.outcome, ProbStep.fresh, bindK_fTransform, fTransform_fTransform,
      Function.comp_def]
    refine bindK_congr fun km _ => ?_
    rw [Program.probInvoke_inl (a := ((some km, none) : _ × LeftRightCCA.Output M (C × T) .dec))
      (by simp [𝓒.body, callProg, returnProg, ProbStep.inlReply, ProbStep.inrReply,
        ProbStep.tagged])]
  | some km =>
    rw [Program.probInvoke_inl (a := ((some km, none) : _ × LeftRightCCA.Output M (C × T) .dec))
      (by simp [𝓒.body, returnProg])]
    simp [keyLaw]

omit [DecidableEq Ke] [DecidableEq M] [DecidableEq T] in
/-- After a step of `𝓒`, its key `k_m` is sampled. -/
lemma 𝓒.mem_support_step (mac : MAC Km C T) {s : Option Km} {o : LeftRightCCA.Port}
    {u : LeftRightCCA.Input M (C × T) o}
    {p : (Option Km × (RC × (Unit × Unit))) × LeftRightCCA.Output M (C × T) o}
    (hp : p ∈ ((𝓒.body M C mac).probCombine
        (ProbStep.parallel stepC (ProbStep.parallel (ProbStep.fresh (𝓒.law1 M C mac))
          (ProbStep.fresh (𝓒.law2 M C mac)))) (𝓒.bound_spec M C mac)
        (s, (r, ((), ()))) o u).1.support) :
    ∃ km, p.1.1 = some km := by
  cases o with
  | enc =>
    obtain ⟨mL, mR⟩ := u
    rw [𝓒.step_enc mac rfl] at hp
    obtain ⟨km, -, hp⟩ := mem_support_bindK hp
    obtain ⟨rc, -, hp⟩ := mem_support_bindK hp
    obtain ⟨t, -, rfl⟩ := mem_support_fTransform _ _ hp
    exact ⟨km, rfl⟩
  | dec =>
    rw [𝓒.step_dec mac u] at hp
    obtain ⟨km, -, hp⟩ := mem_support_bindK hp
    exact ⟨km, by rw [((Finsupp.mem_support_single _ _ _).mp hp).1]⟩

end CallingPrograms

/-! ### Fresh sampling and the hops -/

section FreshSampling

open Probability.Distribution

/-- `π_EtM` on `⟦E_k, D_k⟧ ∥ ⟦S_k, V_k⟧` as fresh sampling. -/
noncomputable def 𝓟.freshSamplingReal (scheme : SymmetricEncryption Ke M C) (mac : MAC Km C T)
    (q : AE.Port → ℕ) :
    FreshSampling (AE.perPort M (C × T) q)
      (𝓟.perLabel q • (AE.Real.perPort scheme ∥ MAC.Real.perPort mac)) :=
  ((AE.Real.freshSampling scheme q).parallel
    (MAC.Real.freshSampling mac (tagBudget q))).ofLabelBoundedProgram
    (A := AE.perPort M (C × T) q) none (𝓟.body M C T) (𝓟.bound_spec M C T) 𝓟.calls
    𝓟.labelBounded q (fun _ hd => hd.2) (𝓟.admits q)

/-- `π_EtM` on `⟦E_k, D_k⟧ ∥ mac-fake` as fresh sampling. -/
noncomputable def 𝓟.freshSamplingSUF (scheme : SymmetricEncryption Ke M C) (mac : MAC Km C T)
    (q : AE.Port → ℕ) :
    FreshSampling (AE.perPort M (C × T) q)
      (𝓟.perLabel q • (AE.Real.perPort scheme ∥ MAC.SUF.perPort C T • MAC.Real.perPort mac)) :=
  ((AE.Real.freshSampling scheme q).parallel
    (MAC.SUF.freshSamplingReal mac (tagBudget q))).ofLabelBoundedProgram
    (A := AE.perPort M (C × T) q) none (𝓟.body M C T) (𝓟.bound_spec M C T) 𝓟.calls
    𝓟.labelBounded q (fun _ hd => hd.2) (𝓟.admits q)

/-- `π_enc` on `E_k ∥ ⟦S_k, V_k⟧` as fresh sampling. -/
noncomputable def 𝓟ₑ.freshSamplingReal (scheme : SymmetricEncryption Ke M C) (mac : MAC Km C T)
    (q : Encryption.Port → ℕ) :
    FreshSampling (Encryption.perPort M (C × T) q)
      (𝓟ₑ.perLabel q • (Encryption.Real.perPort scheme ∥ MAC.Real.perPort mac)) :=
  ((Encryption.Real.freshSampling scheme q).parallel
    (MAC.Real.freshSampling mac (encTagBudget q))).ofLabelBoundedProgram
    (A := Encryption.perPort M (C × T) q) none (𝓟ₑ.body M C T) (𝓟ₑ.bound_spec M C T) 𝓟ₑ.calls
    𝓟ₑ.labelBounded q (fun _ hd => hd.2) (𝓟ₑ.admits q)

/-- `π_enc` on `ρ^cpa(E_k) ∥ ⟦S_k, V_k⟧` as fresh sampling. -/
noncomputable def 𝓟ₑ.freshSamplingCPA [Nonempty M] (scheme : SymmetricEncryption Ke M C)
    (mac : MAC Km C T) (q : Encryption.Port → ℕ) :
    FreshSampling (Encryption.perPort M (C × T) q)
      (𝓟ₑ.perLabel q • (ρ^cpa • Encryption.Real.perPort scheme ∥ MAC.Real.perPort mac)) :=
  ((Encryption.CPA.freshSamplingReal scheme q).parallel
    (MAC.Real.freshSampling mac (encTagBudget q))).ofLabelBoundedProgram
    (A := Encryption.perPort M (C × T) q) none (𝓟ₑ.body M C T) (𝓟ₑ.bound_spec M C T) 𝓟ₑ.calls
    𝓟ₑ.labelBounded q (fun _ hd => hd.2) (𝓟ₑ.admits q)

/-- `ρ^cpa(π_enc • (E_k ∥ ⟦S_k, V_k⟧))` as fresh sampling. -/
noncomputable def cpaFreshSampling [Nonempty M] (scheme : SymmetricEncryption Ke M C)
    (mac : MAC Km C T) (q : Encryption.Port → ℕ) :
    FreshSampling (Encryption.perPort M (C × T) q)
      (ρ^cpa • (𝓟ₑ.perLabel q • (Encryption.Real.perPort scheme ∥ MAC.Real.perPort mac))) :=
  FreshSampling.ofRightContext _
    (((𝓟ₑ.freshSamplingReal scheme mac q).parallel
      (FreshSampling.source (Encryption.CPA.law1 M (C × T)) _)).ofPreservingProgram
        none _ _ _ _ _ _ _)

/-- `𝓜 b` on a tagging resource with a presentation, as fresh sampling. -/
noncomputable def 𝓜.freshSampling (scheme : SymmetricEncryption Ke M C) (b : Bool)
    {q : LeftRightCCA.Port → ℕ} {R : Resource (Tagging.perPort C T (𝓜.insideBudget T scheme b q))}
    (Φ : FreshSampling (Tagging.perPort C T (𝓜.insideBudget T scheme b q)) R) :
    FreshSampling (LeftRightCCA.perPort M (C × T) q) (𝓜.perPort T scheme b • R) :=
  FreshSampling.ofRightContext _
    ((Φ.parallel ((FreshSampling.source (𝓜.law1 T scheme b) _).parallel
      (FreshSampling.source (𝓜.law2 T scheme b) _))).ofPreservingProgram none _ _ _ _ _ _ _)

/-- `𝓒` on a left-or-right resource with a presentation, as fresh sampling. -/
noncomputable def 𝓒.freshSampling (mac : MAC Km C T) {q : LeftRightCCA.Port → ℕ}
    {R : Resource (LeftRight.perPort M C (𝓒.insideBudget M C mac q))}
    (Φ : FreshSampling (LeftRight.perPort M C (𝓒.insideBudget M C mac q)) R) :
    FreshSampling (LeftRightCCA.perPort M (C × T) q) (𝓒.perPort M C mac • R) :=
  FreshSampling.ofRightContext _
    ((Φ.parallel ((FreshSampling.source (𝓒.law1 M C mac) _).parallel
      (FreshSampling.source (𝓒.law2 M C mac) _))).ofPreservingProgram none _ _ _ _ _ _ _)

/-- **The keys of encrypt-then-MAC for the keys of the two schemes**: none before either is
sampled, the pair once both are, and otherwise the pair with the missing key sampled now. -/
noncomputable def deferredKeys (scheme : SymmetricEncryption Ke M C) (mac : MAC Km C T) :
    Option Ke → Option Km → Distribution.ProbDist (Option (Ke × Km))
  | none, none => Distribution.ProbDist.single none
  | some ke, some km => Distribution.ProbDist.single (some (ke, km))
  | none, some km => Distribution.ProbDist.map (fun ke => some (ke, km)) scheme.gen
  | some ke, none => Distribution.ProbDist.map (fun km => some (ke, km)) mac.gen

/-- **The reachable states of `ρ^ctxt(E_k)`** of encrypt-then-MAC: the table is empty until the
first encryption, which samples the keys; from then on each recorded ciphertext `(c', T)` of a
message `m` has `c'` an encryption of `m` under `k_e` and `T` a tag of `c'` under `k_m`. -/
def ctxtInvariant (scheme : SymmetricEncryption Ke M C) (mac : MAC Km C T) :
    Option (List (M × (C × T))) → Option (Ke × Km) → Prop
  | none, none => True
  | none, some _ => False
  | some table, none => table = []
  | some table, some (ke, km) => ke ∈ scheme.gen.1.support ∧ km ∈ mac.gen.1.support ∧
      ∀ e ∈ table, e.2.1 ∈ (scheme.enc ke e.1).1.support ∧ e.2.2 ∈ (mac.tag km e.2.1).1.support

/-- **The states of `π_EtM • (⟦E_k, D_k⟧ ∥ mac-fake)` for a state of `ρ^ctxt(E_k)`**: the tagged
pairs of `mac-fake` are the ciphertexts of the table and the keys are those of encrypt-then-MAC;
`k_m`, which `mac-fake` samples at a verification before the first encryption, is sampled now. -/
noncomputable def ctxtKernel (mac : MAC Km C T) :
    Option (List (M × (C × T))) → Option (Ke × Km) →
      Distribution.ProbDist (Option Unit × ((Option Ke × (Unit × Unit)) ×
        (Option (List (C × T)) × (Option Km × (Unit × Unit)))))
  | none, none => Distribution.ProbDist.single (none, ((none, ((), ())), (none, (none, ((), ())))))
  | some table, none => Distribution.ProbDist.map (fun km =>
      (some (), ((none, ((), ())), (some (table.map Prod.snd), (some km, ((), ())))))) mac.gen
  | table, some (ke, km) => Distribution.ProbDist.single ((table.map fun _ => ()),
      ((some ke, ((), ())), (table.map (List.map Prod.snd), (some km, ((), ())))))

omit [Fintype Ke] [Fintype Km] [Fintype M] [Fintype T] [DecidableEq Ke] [DecidableEq Km]
  [DecidableEq M] [DecidableEq T] in
/-- An encryption of encrypt-then-MAC is an encryption `c'` of `Σ_e` with a tag of `c'`. -/
lemma mem_support_enc {scheme : SymmetricEncryption Ke M C} {mac : MAC Km C T} {k : Ke × Km}
    {m : M} {c : C × T} (hc : c ∈ ((EncryptThenMAC scheme mac).enc k m).1.support) :
    c.1 ∈ (scheme.enc k.1 m).1.support ∧ c.2 ∈ (mac.tag k.2 c.1).1.support := by
  obtain ⟨c', hc', hc⟩ := Distribution.ProbDist.mem_support_bind hc
  obtain ⟨t, ht, rfl⟩ := Distribution.ProbDist.mem_support_map hc
  exact ⟨hc', ht⟩

omit [Fintype Ke] [Fintype Km] [Fintype M] [Fintype C] [Fintype T] [DecidableEq Ke]
  [DecidableEq Km] [DecidableEq M] in
/-- **With correct schemes, replaying the table is decrypting the issued pairs**: on a table of
encryptions and tags under `k_e` and `k_m`, the first message recorded with `(c', T)` is the
decryption of `c'` if `(c', T)` verifies and was issued, and `⊥` otherwise. -/
lemma replay_eq {scheme : SymmetricEncryption Ke M C} {mac : MAC Km C T}
    (schemeCorrect : scheme.Correct) (macCorrect : mac.Correct) {ke : Ke} {km : Km}
    (hke : ke ∈ scheme.gen.1.support) (hkm : km ∈ mac.gen.1.support)
    {table : List (M × (C × T))}
    (htable : ∀ e ∈ table,
      e.2.1 ∈ (scheme.enc ke e.1).1.support ∧ e.2.2 ∈ (mac.tag km e.2.1).1.support)
    (c : C) (t : T) :
    AE.replay table (c, t) =
      if mac.verify km c t && decide ((c, t) ∈ table.map Prod.snd) then scheme.dec ke c
      else none := by
  cases hr : AE.replay table (c, t) with
  | none =>
    have hn := List.find?_eq_none.mp (Option.map_eq_none_iff.mp hr)
    have hmem : (c, t) ∉ table.map Prod.snd := fun hmem => by
      obtain ⟨e, he, hec⟩ := List.mem_map.mp hmem
      exact hn e he (by simp [hec])
    simp [hmem]
  | some m =>
    obtain ⟨e, hfind, rfl⟩ := Option.map_eq_some_iff.mp hr
    have he := List.mem_of_find?_eq_some hfind
    have hec : e.2 = (c, t) := by simpa using List.find?_some hfind
    obtain ⟨hc, ht⟩ := htable e he
    rw [hec] at hc ht
    have hmem : (c, t) ∈ table.map Prod.snd := List.mem_map.mpr ⟨e, he, hec⟩
    simp [hmem, macCorrect km hkm c t ht, schemeCorrect ke hke e.1 c hc]

omit [DecidableEq T] in
/-- **Encrypt-then-MAC is `π_EtM` on the two schemes**: `⟦E_k, D_k⟧` of encrypt-then-MAC, for the
pair of independent keys, is `π_EtM` attached to `⟦E_k, D_k⟧ ∥ ⟦S_k, V_k⟧`. -/
lemma real_eq (scheme : SymmetricEncryption Ke M C) (mac : MAC Km C T) (q : AE.Port → ℕ) :
    AE.Real.perPort (EncryptThenMAC scheme mac) (budget := q) =
      𝓟.perLabel q • (AE.Real.perPort scheme ∥ MAC.Real.perPort mac) := by
  refine (AE.Real.freshSampling (EncryptThenMAC scheme mac) q).eq_fresh.trans
    (Eq.trans ?_ (𝓟.freshSamplingReal scheme mac q).eq_fresh.symm)
  -- `⟦E_k, D_k⟧` of `Σ_e` samples `k_e` at its first call: the kernel samples it while it has not.
  symm
  refine Resource.ofProbAutomaton_eq_of_simulation _ _ _ _
    (fun s => Distribution.ProbDist.map (fun o => (o, ((), ())))
      (deferredKeys scheme mac s.2.1.1 s.2.2.1))
    (fun _ _ => True) (fun _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) ?_ ?_ <;>
    dsimp only [𝓟.freshSamplingReal, AE.Real.freshSampling, MAC.Real.freshSampling,
      FreshSampling.ofProgram, FreshSampling.ofLabelBoundedProgram, FreshSampling.parallel,
      FreshSampling.source, id, Distribution.ProbDist.single, Distribution.ProbDist.map]
  · rintro - ⟨p, ⟨a, ⟨⟩, ⟨⟩⟩, ⟨r, ⟨⟩, ⟨⟩⟩⟩ ⟨_ | _, x⟩ - -
    · unfold ProbStep.SimulatesAt
      conv_rhs => rw [ProbStep.outcome,
        𝓟.step_enc (AE.Real.step_enc scheme _ x) (fun c => MAC.Real.step_tag mac _ c)]
      rcases a with _ | ke <;> rcases r with _ | km <;> dsimp only <;>
        simp only [deferredKeys, Distribution.ProbDist.single, Distribution.ProbDist.map,
          fTransform_single, bindK_single, one_smul, bindK_fTransform, Function.comp_def]
      · rw [ProbStep.outcome, AE.Real.step_enc]
        simp only [keyLaw, EncryptThenMAC, Distribution.prodProbDist_val, prod_eq_bindK,
          bindK_bindK, bindK_fTransform, fTransform_bindK, fTransform_fTransform, Function.comp_def,
          Distribution.ProbDist.bind_val, Distribution.ProbDist.map, fTransform_single,
          bindK_single_comp, ProbStep.tagged]
        refine bindK_congr fun ke _ => ?_
        rw [bindK_comm]
      · conv_lhs => enter [2, ke]; rw [ProbStep.outcome, AE.Real.step_enc]
        simp only [keyLaw, EncryptThenMAC, bindK_bindK, bindK_fTransform, fTransform_bindK,
          fTransform_fTransform, Function.comp_def, Distribution.ProbDist.bind_val,
          Distribution.ProbDist.map, bindK_single, one_smul, fTransform_single, bindK_single_comp,
          ProbStep.tagged]
      · conv_lhs => enter [2, km]; rw [ProbStep.outcome, AE.Real.step_enc]
        simp only [keyLaw, EncryptThenMAC, bindK_bindK, bindK_fTransform, fTransform_bindK,
          fTransform_fTransform, Function.comp_def, Distribution.ProbDist.bind_val,
          Distribution.ProbDist.map, bindK_single, one_smul, fTransform_single, bindK_single_comp,
          ProbStep.tagged]
        rw [bindK_comm]
      · rw [ProbStep.outcome, AE.Real.step_enc]
        simp only [keyLaw, EncryptThenMAC, bindK_bindK, bindK_fTransform, fTransform_bindK,
          fTransform_fTransform, Function.comp_def, Distribution.ProbDist.bind_val,
          Distribution.ProbDist.map, bindK_single, one_smul, fTransform_single, bindK_single_comp,
          ProbStep.tagged]
    · obtain ⟨c, t⟩ := x
      unfold ProbStep.SimulatesAt
      conv_rhs => rw [ProbStep.outcome,
        𝓟.step_dec (AE.Real.step_dec scheme _ c) (MAC.Real.step_verify mac _ c t)]
      rcases a with _ | ke <;> rcases r with _ | km <;> dsimp only <;>
        simp only [deferredKeys, Distribution.ProbDist.single, Distribution.ProbDist.map,
          fTransform_single, bindK_single, one_smul, bindK_fTransform, Function.comp_def]
      · rw [ProbStep.outcome, AE.Real.step_dec]
        simp only [keyLaw, EncryptThenMAC, Distribution.prodProbDist_val, prod_eq_bindK,
          bindK_bindK, bindK_fTransform, fTransform_bindK, fTransform_fTransform, Function.comp_def,
          Distribution.ProbDist.map, bindK_single, one_smul, ite_bindK, fTransform_single,
          bindK_single_comp, ProbStep.tagged]
        rw [bindK_fTransform_comm]
        refine bindK_congr fun km _ => ?_
        by_cases hv : mac.verify km c t = true <;> simp only [hv, Bool.false_eq_true, ↓reduceIte]
      · conv_lhs => enter [2, ke]; rw [ProbStep.outcome, AE.Real.step_dec]
        simp only [keyLaw, EncryptThenMAC, bindK_fTransform, fTransform_fTransform,
          Function.comp_def, Distribution.ProbDist.map, bindK_single, one_smul, ite_bindK,
          fTransform_single, bindK_single_comp, ProbStep.tagged]
        by_cases hv : mac.verify km c t = true <;> simp only [hv, Bool.false_eq_true, ↓reduceIte]
      · conv_lhs => enter [2, km]; rw [ProbStep.outcome, AE.Real.step_dec]
        simp only [keyLaw, EncryptThenMAC, bindK_bindK, bindK_fTransform, fTransform_fTransform,
          Function.comp_def, Distribution.ProbDist.map, bindK_single, one_smul, ite_bindK,
          fTransform_single, bindK_single_comp, ProbStep.tagged]
        rw [fTransform_eq_bindK]
        refine bindK_congr fun km _ => ?_
        by_cases hv : mac.verify km c t = true <;> simp only [hv, Bool.false_eq_true, ↓reduceIte]
      · rw [ProbStep.outcome, AE.Real.step_dec]
        simp only [keyLaw, EncryptThenMAC, fTransform_fTransform, Function.comp_def,
          Distribution.ProbDist.map, bindK_single, one_smul, ite_bindK, fTransform_single,
          bindK_single_comp, ProbStep.tagged]
        by_cases hv : mac.verify km c t = true <;> simp only [hv, Bool.false_eq_true, ↓reduceIte]
  · rw [bindK_single, one_smul]
    dsimp only
    simp only [deferredKeys, Distribution.ProbDist.single, fTransform_single]

omit [DecidableEq T] in
/-- **The encryption of encrypt-then-MAC is `π_enc` on the two schemes.** -/
lemma encryptionReal_eq (scheme : SymmetricEncryption Ke M C) (mac : MAC Km C T)
    (q : Encryption.Port → ℕ) :
    Encryption.Real.perPort (EncryptThenMAC scheme mac) (budget := q) =
      𝓟ₑ.perLabel q • (Encryption.Real.perPort scheme ∥ MAC.Real.perPort mac) := by
  refine (Encryption.Real.freshSampling (EncryptThenMAC scheme mac) q).eq_fresh.trans
    (Eq.trans ?_ (𝓟ₑ.freshSamplingReal scheme mac q).eq_fresh.symm)
  -- The key pair `k_e ‖ k_m` is the pair of the keys of `E_k` and `⟦S_k, V_k⟧`.
  refine Resource.ofProbAutomaton_eq_of_map _ _ _ _
    (fun s => (s.1.map fun _ => (), ((s.1.map Prod.fst, ((), ())), (s.1.map Prod.snd, ((), ())))))
    ?_ ?_ <;>
    dsimp only [𝓟ₑ.freshSamplingReal, Encryption.Real.freshSampling, MAC.Real.freshSampling,
      FreshSampling.ofProgram, FreshSampling.ofLabelBoundedProgram, FreshSampling.parallel,
      FreshSampling.source, id, Distribution.ProbDist.single]
  · rintro ⟨_ | ⟨ke, km⟩, ⟨⟩, ⟨⟩⟩ ⟨⟨⟩, m⟩
    · simp only [ProbStep.outcome]
      rw [𝓟ₑ.step_enc (Encryption.Real.step_enc scheme _ m) (fun c => MAC.Real.step_tag mac _ c),
        Encryption.Real.step_enc]
      simp only [Option.map, keyLaw, EncryptThenMAC, Distribution.prodProbDist_val, prod_eq_bindK,
        bindK_bindK, bindK_fTransform, fTransform_bindK, fTransform_fTransform, Function.comp_def,
        Distribution.ProbDist.bind_val, Distribution.ProbDist.map]
      refine bindK_congr fun ke _ => ?_
      rw [bindK_comm]
      exact bindK_congr fun km _ => bindK_congr fun c _ => rfl
    · simp only [ProbStep.outcome]
      rw [𝓟ₑ.step_enc (Encryption.Real.step_enc scheme _ m) (fun c => MAC.Real.step_tag mac _ c),
        Encryption.Real.step_enc]
      simp only [Option.map, keyLaw, EncryptThenMAC, bindK_single, one_smul, bindK_fTransform,
        fTransform_bindK, fTransform_fTransform, Function.comp_def, Distribution.ProbDist.bind_val,
        Distribution.ProbDist.map]
      exact bindK_congr fun c _ => rfl
  · rw [fTransform_single]
    rfl

/-- **With the fake MAC, encrypt-then-MAC is `ρ^ctxt`**: only issued ciphertexts verify, and by
correctness of both schemes each decrypts to the message it was issued for. -/
lemma suf_eq_ctxt (scheme : SymmetricEncryption Ke M C) (mac : MAC Km C T)
    (schemeCorrect : scheme.Correct) (macCorrect : mac.Correct) (q : AE.Port → ℕ) :
    𝓟.perLabel q • (AE.Real.perPort scheme ∥ MAC.SUF.perPort C T • MAC.Real.perPort mac) =
      ρ^ctxt • Encryption.Real.perPort (EncryptThenMAC scheme mac) := by
  refine (𝓟.freshSamplingSUF scheme mac q).eq_fresh.trans
    (Eq.trans ?_ (AE.CTXT.freshSamplingReal (EncryptThenMAC scheme mac) q).eq_fresh.symm)
  -- `mac-fake` samples `k_m` at its first call: the kernel samples it before the first encryption.
  symm
  refine Resource.ofProbAutomaton_eq_of_simulation _ _ _ _ (fun s => ctxtKernel mac s.1 s.2.1)
    (fun _ s => ctxtInvariant scheme mac s.1 s.2.1) ?_ ?_ ?_ ?_ <;>
    dsimp only [𝓟.freshSamplingSUF, AE.CTXT.freshSamplingReal, AE.Real.freshSampling,
      MAC.SUF.freshSamplingReal, MAC.Real.freshSampling, Encryption.Real.freshSampling,
      FreshSampling.ofPreservingProgram, FreshSampling.ofProgram,
      FreshSampling.ofLabelBoundedProgram, FreshSampling.parallel, FreshSampling.source, id,
      Distribution.ProbDist.single]
  · rintro s hs
    obtain rfl := ((Finsupp.mem_support_single _ _ _).mp hs).1
    trivial
  · rintro xs ⟨ctxt, o, ⟨⟩, ⟨⟩⟩ ⟨_ | _, x⟩ hinv - p hp
    · rw [AE.CTXT.outcome_enc, ProbStep.outcome] at hp
      obtain ⟨y, hy, rfl⟩ := mem_support_fTransform _ _ hp
      obtain ⟨z, hz, rfl⟩ := mem_support_fTransform _ _ hy
      obtain ⟨k, hk, hz1, hz2⟩ :=
        Encryption.Real.mem_support_step_enc (EncryptThenMAC scheme mac) o x hz
      obtain ⟨ke, km⟩ := k
      obtain ⟨zs, zc⟩ := z
      obtain rfl : zs = (some (ke, km), ((), ())) := congrArg Prod.fst hz1
      obtain ⟨hc1, hc2⟩ := mem_support_enc hz2
      have hnew : ∀ e ∈ [(x, zc)], e.2.1 ∈ (scheme.enc ke e.1).1.support ∧
          e.2.2 ∈ (mac.tag km e.2.1).1.support := fun e he => by
        rw [List.mem_singleton] at he
        subst he
        exact ⟨hc1, hc2⟩
      dsimp only [ProbStep.tagged, Encryption.ciphertextOf]
      rcases ctxt with _ | table <;> rcases o with _ | ⟨ke₀, km₀⟩
      · have hk' : (ke, km) ∈ (Distribution.prod scheme.gen.1 mac.gen.1).support := hk
        obtain ⟨hke, hkm⟩ := Finset.mem_product.mp (Distribution.support_prod_subset _ _ hk')
        exact ⟨hke, hkm, by simpa using hnew⟩
      · exact hinv.elim
      · obtain rfl : table = [] := hinv
        have hk' : (ke, km) ∈ (Distribution.prod scheme.gen.1 mac.gen.1).support := hk
        obtain ⟨hke, hkm⟩ := Finset.mem_product.mp (Distribution.support_prod_subset _ _ hk')
        exact ⟨hke, hkm, by simpa using hnew⟩
      · obtain ⟨hke₀, hkm₀, htable⟩ := hinv
        have hk' : (ke, km) ∈ (Finsupp.single (ke₀, km₀) (1 : ℝ)).support := hk
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj ((Finsupp.mem_support_single _ _ _).mp hk').1
        refine ⟨hke₀, hkm₀, fun e he => ?_⟩
        rcases List.mem_append.mp he with he | he
        · exact htable e he
        · exact hnew e he
    · rw [AE.CTXT.outcome_dec] at hp
      obtain rfl := ((Finsupp.mem_support_single _ _ _).mp hp).1
      rcases ctxt with _ | table <;> rcases o with _ | ⟨ke₀, km₀⟩
      · rfl
      · exact hinv.elim
      · exact hinv
      · exact hinv
  · rintro xs ⟨ctxt, o, ⟨⟩, ⟨⟩⟩ ⟨_ | _, x⟩ hinv -
    · unfold ProbStep.SimulatesAt
      conv_rhs => rw [AE.CTXT.outcome_enc, ProbStep.outcome, Encryption.Real.step_enc]
      rcases ctxt with _ | table <;> rcases o with _ | ⟨ke, km⟩
      · dsimp only [ctxtKernel, Distribution.ProbDist.single]
        rw [bindK_single, one_smul, ProbStep.outcome, 𝓟.step_enc (AE.Real.step_enc scheme _ x)
          (fun c => MAC.SUF.step_tag (MAC.Real.step_tag mac _ c))]
        simp only [keyLaw, EncryptThenMAC, Distribution.prodProbDist_val, prod_eq_bindK,
          bindK_bindK, bindK_fTransform, fTransform_bindK, fTransform_fTransform, Function.comp_def,
          Distribution.ProbDist.bind_val, Distribution.ProbDist.map, fTransform_single,
          bindK_single_comp, ProbStep.tagged, Encryption.ciphertextOf, Option.getD, List.nil_append,
          List.map_cons, List.map_nil, Option.map]
        refine bindK_congr fun ke _ => ?_
        rw [bindK_comm]
      · exact hinv.elim
      · obtain rfl : table = [] := hinv
        dsimp only [ctxtKernel, Distribution.ProbDist.map]
        simp only [bindK_fTransform, Function.comp_def]
        conv_lhs => enter [2, km]; rw [ProbStep.outcome, 𝓟.step_enc (AE.Real.step_enc scheme _ x)
          (fun c => MAC.SUF.step_tag (MAC.Real.step_tag mac _ c))]
        simp only [keyLaw, EncryptThenMAC, Distribution.prodProbDist_val, prod_eq_bindK,
          bindK_bindK, bindK_fTransform, fTransform_bindK, fTransform_fTransform, Function.comp_def,
          Distribution.ProbDist.bind_val, Distribution.ProbDist.map, bindK_single, one_smul,
          fTransform_single, Distribution.ProbDist.single, bindK_single_comp, ProbStep.tagged,
          Encryption.ciphertextOf, Option.getD, List.nil_append, List.map_cons, List.map_nil,
          Option.map]
        rw [bindK_comm]
      · dsimp only [ctxtKernel, Distribution.ProbDist.single]
        rw [bindK_single, one_smul, ProbStep.outcome, 𝓟.step_enc (AE.Real.step_enc scheme _ x)
          (fun c => MAC.SUF.step_tag (MAC.Real.step_tag mac _ c))]
        simp only [keyLaw, EncryptThenMAC, bindK_bindK, bindK_fTransform, fTransform_bindK,
          fTransform_fTransform, Function.comp_def, Distribution.ProbDist.bind_val,
          Distribution.ProbDist.map, bindK_single, one_smul, fTransform_single, bindK_single_comp,
          ProbStep.tagged, Encryption.ciphertextOf, Option.getD, List.map_cons, List.map_nil,
          List.map_append, Option.map]
    · obtain ⟨c, t⟩ := x
      unfold ProbStep.SimulatesAt
      conv_rhs => rw [AE.CTXT.outcome_dec]
      rcases ctxt with _ | table <;> rcases o with _ | ⟨ke, km⟩
      · dsimp only [ctxtKernel, Distribution.ProbDist.single]
        rw [bindK_single, one_smul, ProbStep.outcome, 𝓟.step_dec (AE.Real.step_dec scheme _ c)
          (MAC.SUF.step_verify (MAC.Real.step_verify mac _ c t))]
        simp only [keyLaw, bindK_fTransform, fTransform_fTransform, Function.comp_def,
          Distribution.ProbDist.map, bindK_single, one_smul, bindK_single_comp, ProbStep.tagged,
          Option.getD, List.map_nil, Option.map, AE.replay, List.find?_nil, List.not_mem_nil,
          decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      · exact hinv.elim
      · obtain rfl : table = [] := hinv
        dsimp only [ctxtKernel, Distribution.ProbDist.map]
        simp only [bindK_fTransform, Function.comp_def]
        conv_lhs => enter [2, km]; rw [ProbStep.outcome, 𝓟.step_dec (AE.Real.step_dec scheme _ c)
          (MAC.SUF.step_verify (MAC.Real.step_verify mac _ c t))]
        simp only [keyLaw, fTransform_fTransform, Function.comp_def, bindK_single, one_smul,
          fTransform_single, Distribution.ProbDist.single, bindK_single_comp, ProbStep.tagged,
          Option.getD, List.map_nil, Option.map, AE.replay, List.find?_nil, List.not_mem_nil,
          decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      · obtain ⟨hke, hkm, htable⟩ := hinv
        dsimp only [ctxtKernel, Distribution.ProbDist.single]
        rw [bindK_single, one_smul, ProbStep.outcome, 𝓟.step_dec (AE.Real.step_dec scheme _ c)
          (MAC.SUF.step_verify (MAC.Real.step_verify mac _ c t))]
        simp only [keyLaw, Distribution.ProbDist.map, bindK_single, one_smul, fTransform_single,
          bindK_single_comp, Option.getD, Option.map]
        rw [replay_eq schemeCorrect macCorrect hke hkm htable c t]
        split_ifs <;> rw [fTransform_single] <;> rfl
  · rw [bindK_single, one_smul]
    rfl

omit [DecidableEq T] in
/-- **`π_enc` commutes with `ρ^cpa`**: replacing the message before encrypting is replacing it
before encrypt-then-MAC. -/
lemma cpa_comm [Nonempty M] (scheme : SymmetricEncryption Ke M C) (mac : MAC Km C T)
    (q : Encryption.Port → ℕ) :
    𝓟ₑ.perLabel q • (ρ^cpa • Encryption.Real.perPort scheme ∥ MAC.Real.perPort mac) =
      ρ^cpa • (𝓟ₑ.perLabel q • (Encryption.Real.perPort scheme ∥ MAC.Real.perPort mac)) := by
  refine (𝓟ₑ.freshSamplingCPA scheme mac q).eq_fresh.trans
    (Eq.trans ?_ (cpaFreshSampling scheme mac q).eq_fresh.symm)
  -- The state of `ρ^cpa` moves from inside `π_enc` to outside it.
  refine Resource.ofProbAutomaton_eq_of_map _ _ _ _
    (fun s => (s.2.1.1, ((s.1, (s.2.1.2.1, s.2.2)), ()))) ?_ ?_ <;>
    dsimp only [𝓟ₑ.freshSamplingCPA, cpaFreshSampling, 𝓟ₑ.freshSamplingReal,
      Encryption.CPA.freshSamplingReal, Encryption.Real.freshSampling, MAC.Real.freshSampling,
      FreshSampling.ofRightContext, FreshSampling.cast, FreshSampling.ofPreservingProgram,
      FreshSampling.ofProgram, FreshSampling.ofLabelBoundedProgram, FreshSampling.parallel,
      FreshSampling.source, id, Distribution.ProbDist.single]
  · rintro ⟨p, ⟨c, e, ⟨⟩⟩, r⟩ ⟨⟨⟩, m⟩
    rw [Encryption.CPA.outcome_enc]
    conv_rhs => rw [ProbStep.outcome,
      𝓟ₑ.step_enc (Encryption.val_eq_outcome _ _ _) (fun _ => rfl), Encryption.CPA.outcome_enc]
    simp only [fTransform_bindK, bindK_fTransform, bindK_bindK, fTransform_fTransform,
      Function.comp_def]
    refine bindK_congr fun m' _ => ?_
    conv_lhs => rw [ProbStep.outcome,
      𝓟ₑ.step_enc (Encryption.val_eq_outcome _ _ _) (fun _ => rfl)]
    simp only [fTransform_bindK, bindK_fTransform, fTransform_fTransform, Function.comp_def]
    exact bindK_congr fun p₁ _ => rfl
  · rw [fTransform_single]

/-- **The states of `𝓜 b • mac-real` for a state of `cca-b`**: `𝒟` is that of `𝓜 b`, and the key
`k_e ‖ k_m` is the key `k_e` of `𝓜 b` with the key `k_m` of `mac-real`; with `𝒟` and no key, `𝓜 b`
holds a key `k_e` sampled now. -/
noncomputable def ccaKernel (scheme : SymmetricEncryption Ke M C) :
    Option (List (C × T)) → Option (Ke × Km) →
      Distribution.ProbDist (Option (Ke × List (C × T)) ×
        ((Option Km × (Unit × Unit)) × (Unit × Unit)))
  | D, some (ke, km) =>
    Distribution.ProbDist.single (some (ke, D.getD []), ((some km, ((), ())), ((), ())))
  | some D, none => Distribution.ProbDist.map
      (fun ke => (some (ke, D), ((none, ((), ())), ((), ())))) scheme.gen
  | none, none => Distribution.ProbDist.single (none, ((none, ((), ())), ((), ())))

/-- **`cca-b` is `𝓜 b` on `mac-real`**: the key `k_e ‖ k_m` of encrypt-then-MAC is the key `k_e`
of `𝓜 b` with the key `k_m` of `mac-real`. -/
lemma cca_eq (scheme : SymmetricEncryption Ke M C) (mac : MAC Km C T)
    (q : LeftRightCCA.Port → ℕ) (b : Bool) :
    (if b then (Encryption.LORCCA.systems (EncryptThenMAC scheme mac) q).2
      else (Encryption.LORCCA.systems (EncryptThenMAC scheme mac) q).1) =
      𝓜.perPort T scheme b • MAC.Real.perPort mac := by
  -- `𝓜 b` samples `k_e` at its first call, which tags or verifies, so that `mac-real` samples
  -- `k_m` then too: the kernel splits the key `k_e ‖ k_m` of `cca-b`.
  refine Eq.trans ?_ (𝓜.freshSampling scheme b (MAC.Real.freshSampling mac _)).eq_fresh.symm
  cases b <;> [refine
      (Encryption.LeftCCA.freshSamplingReal (EncryptThenMAC scheme mac) q).eq_fresh.trans ?_;
    refine
      (Encryption.RightCCA.freshSamplingReal (EncryptThenMAC scheme mac) q).eq_fresh.trans ?_] <;>
  · refine Resource.ofProbAutomaton_eq_of_simulation _ _ _ _
        (fun s => ccaKernel scheme s.1 s.2.1) (fun _ _ => True) (fun _ _ => trivial)
        (fun _ _ _ _ _ _ _ => trivial) ?_ ?_ <;>
      dsimp only [Encryption.LeftCCA.freshSamplingReal, Encryption.RightCCA.freshSamplingReal,
        𝓜.freshSampling, AE.Real.freshSampling, MAC.Real.freshSampling,
        FreshSampling.ofRightContext, FreshSampling.cast, FreshSampling.ofPreservingProgram,
        FreshSampling.ofProgram, FreshSampling.parallel, FreshSampling.source, id,
        Distribution.ProbDist.single]
    · rintro - ⟨D, k, ⟨⟩, ⟨⟩⟩ ⟨_ | _, x⟩ - -
      · obtain ⟨mL, mR⟩ := x
        unfold ProbStep.SimulatesAt
        conv_rhs => rw [ProbStep.outcome]
        first
          | rw [Encryption.LeftCCA.step_enc (AE.Real.step_enc (EncryptThenMAC scheme mac) _ mL)]
          | rw [Encryption.RightCCA.step_enc (AE.Real.step_enc (EncryptThenMAC scheme mac) _ mR)]
        rcases D with _ | D <;> rcases k with _ | ⟨ke, km⟩ <;> dsimp only <;>
          simp only [ccaKernel, Distribution.ProbDist.single, Distribution.ProbDist.map,
            bindK_single, one_smul, bindK_fTransform, Function.comp_def]
        · rw [ProbStep.outcome, 𝓜.step_enc scheme _ (fun c => MAC.Real.step_tag mac _ c)]
          simp only [keyLaw, EncryptThenMAC, Distribution.prodProbDist_val, prod_eq_bindK,
            bindK_bindK, bindK_fTransform, fTransform_bindK, fTransform_fTransform,
            Function.comp_def, Distribution.ProbDist.bind_val, Distribution.ProbDist.map,
            fTransform_single, bindK_single_comp, ProbStep.tagged, Option.map_none,
            Option.getD_none, Option.getD_some, Bool.false_eq_true, ↓reduceIte]
          refine bindK_congr fun ke _ => ?_
          rw [bindK_comm]
        · rw [ProbStep.outcome, 𝓜.step_enc scheme _ (fun c => MAC.Real.step_tag mac _ c)]
          simp only [keyLaw, EncryptThenMAC, Distribution.ProbDist.bind_val, bindK_bindK,
            bindK_fTransform, fTransform_bindK, fTransform_fTransform, Function.comp_def,
            Distribution.ProbDist.map, fTransform_single, bindK_single_comp, ProbStep.tagged,
            Option.map_some, Option.getD_none, Option.getD_some, bindK_single, one_smul,
            Bool.false_eq_true, ↓reduceIte]
        · conv_lhs => enter [2, ke]; rw [ProbStep.outcome,
            𝓜.step_enc scheme _ (fun c => MAC.Real.step_tag mac _ c)]
          simp only [keyLaw, EncryptThenMAC, Distribution.prodProbDist_val, prod_eq_bindK,
            bindK_bindK, bindK_fTransform, fTransform_bindK, fTransform_fTransform,
            Function.comp_def, Distribution.ProbDist.bind_val, Distribution.ProbDist.map,
            fTransform_single, bindK_single_comp, ProbStep.tagged, Option.map_some,
            Option.getD_some, bindK_single, one_smul, Bool.false_eq_true, ↓reduceIte]
          refine bindK_congr fun ke _ => ?_
          rw [bindK_comm]
        · rw [ProbStep.outcome, 𝓜.step_enc scheme _ (fun c => MAC.Real.step_tag mac _ c)]
          simp only [keyLaw, EncryptThenMAC, Distribution.ProbDist.bind_val, bindK_bindK,
            bindK_fTransform, fTransform_bindK, fTransform_fTransform, Function.comp_def,
            Distribution.ProbDist.map, fTransform_single, bindK_single_comp, ProbStep.tagged,
            Option.map_some, Option.getD_some, bindK_single, one_smul, Bool.false_eq_true,
            ↓reduceIte]
      · obtain ⟨c, t⟩ := x
        unfold ProbStep.SimulatesAt
        conv_rhs => rw [ProbStep.outcome]
        first
          | rw [Encryption.LeftCCA.step_dec (AE.Real.step_dec (EncryptThenMAC scheme mac) _ (c, t))]
          | rw [Encryption.RightCCA.step_dec
              (AE.Real.step_dec (EncryptThenMAC scheme mac) _ (c, t))]
        rcases D with _ | D <;> rcases k with _ | ⟨ke, km⟩ <;> dsimp only <;>
          simp only [ccaKernel, Distribution.ProbDist.single, Distribution.ProbDist.map,
            bindK_single, one_smul, bindK_fTransform, Function.comp_def]
        · rw [ProbStep.outcome, 𝓜.step_dec scheme _ (MAC.Real.step_verify mac _ c t)]
          simp only [keyLaw, EncryptThenMAC, Distribution.prodProbDist_val, prod_eq_bindK,
            bindK_bindK, bindK_fTransform, fTransform_bindK, fTransform_fTransform,
            Function.comp_def, Distribution.ProbDist.map, fTransform_single, bindK_single_comp,
            ProbStep.tagged, Option.map_none, Option.getD_none, Option.getD_some,
            List.not_mem_nil, ↓reduceIte]
        · rw [ProbStep.outcome, 𝓜.step_dec scheme _ (MAC.Real.step_verify mac _ c t)]
          simp only [keyLaw, EncryptThenMAC, fTransform_single, ProbStep.tagged, Option.map_some,
            Option.getD_none, Option.getD_some, bindK_single, one_smul, List.not_mem_nil,
            ↓reduceIte]
        · conv_lhs => enter [2, ke]; rw [ProbStep.outcome,
            𝓜.step_dec scheme _ (MAC.Real.step_verify mac _ c t)]
          by_cases hc : (c, t) ∈ D <;>
          simp only [keyLaw, EncryptThenMAC, Distribution.prodProbDist_val, prod_eq_bindK,
            bindK_bindK, bindK_fTransform, fTransform_bindK, fTransform_fTransform,
            Function.comp_def, Distribution.ProbDist.map, fTransform_single, bindK_single_comp,
            ProbStep.tagged, Option.map_some, Option.getD_some, bindK_single, one_smul, hc,
            ↓reduceIte]
        · rw [ProbStep.outcome, 𝓜.step_dec scheme _ (MAC.Real.step_verify mac _ c t)]
          by_cases hc : (c, t) ∈ D <;>
          simp only [keyLaw, EncryptThenMAC, fTransform_single, ProbStep.tagged, Option.map_some,
            Option.getD_some, bindK_single, one_smul, hc, ↓reduceIte]
    · rw [bindK_single, one_smul]
      rfl

/-- **`𝒟` after a reply**: the ciphertext of an encryption is added to `𝒟`. -/
def challengesAfter (D : List (C × T)) (_x : Σ o, LeftRightCCA.Input M (C × T) o) :
    (Σ o, LeftRightCCA.Output M (C × T) o) → List (C × T)
  | ⟨.enc, c⟩ => D ++ [c]
  | ⟨.dec, _⟩ => D

/-- **The states of `𝓜 b • mac-fake` for a state of `𝓒 • cpa-b` with `𝒟`**: the keys are those of
`𝓒` and `E_k`, and both `𝒟` of `𝓜 b` and the tagged pairs of `mac-fake` are `𝒟`; `k_e`, which
`𝓜 b` samples at its first call, is sampled now when `E_k` has not sampled it. -/
noncomputable def fakeKernel (scheme : SymmetricEncryption Ke M C) :
    Option Km → Option Ke → List (C × T) →
      Distribution.ProbDist (Option (Ke × List (C × T)) ×
        ((Option (List (C × T)) × (Option Km × (Unit × Unit))) × (Unit × Unit)))
  | some km, some ke, D =>
    Distribution.ProbDist.single (some (ke, D), ((some D, (some km, ((), ()))), ((), ())))
  | some km, none, D => Distribution.ProbDist.map
      (fun ke => (some (ke, D), ((some D, (some km, ((), ()))), ((), ())))) scheme.gen
  | none, _, _ => Distribution.ProbDist.single (none, ((none, (none, ((), ()))), ((), ())))

/-- **The reachable states of `𝓒 • cpa-b` with `𝒟`**: before the first call of `𝓒`, the key of
`E_k` is not sampled and `𝒟` is empty. -/
def fakeInvariant : Option Km → Option Ke → List (C × T) → Prop
  | none, ke, D => ke = none ∧ D = []
  | some _, _, _ => True

/-- **With the fake MAC, `𝓜 b` decrypts nothing**: the tagged pairs of `mac-fake` are the
ciphertexts of `𝒟`, so a ciphertext outside `𝒟` never verifies, and `𝓜 b` on `mac-fake` is `𝓒`
on `cpa-b`. -/
lemma fake_eq (scheme : SymmetricEncryption Ke M C) (mac : MAC Km C T)
    (q : LeftRightCCA.Port → ℕ) (b : Bool) :
    𝓜.perPort T scheme b • MAC.SUF.perPort C T • MAC.Real.perPort mac =
      𝓒.perPort M C mac •
        (if b then Encryption.Right.perPort M C • Encryption.Real.perPort scheme
          else Encryption.Left.perPort M C • Encryption.Real.perPort scheme :
          Resource (LeftRight.perPort M C (𝓒.insideBudget M C mac q))) := by
  -- `𝓜 b` samples `k_e` at its first call, `E_k` at its first encryption: the kernel samples
  -- `k_e` while `E_k` has not; `𝒟` and the tagged pairs of `mac-fake` are the recorded `𝒟`.
  refine (𝓜.freshSampling scheme b (MAC.SUF.freshSamplingReal mac _)).eq_fresh.trans ?_
  cases b <;> [refine Eq.trans ?_
      (𝓒.freshSampling mac (Encryption.Left.freshSamplingReal scheme _)).eq_fresh.symm;
    refine Eq.trans ?_
      (𝓒.freshSampling mac (Encryption.Right.freshSamplingReal scheme _)).eq_fresh.symm] <;>
  · refine Eq.trans ?_ (Resource.ofProbAutomaton_withRecord _ challengesAfter _ [])
    symm
    refine Resource.ofProbAutomaton_eq_of_simulation _ _ _ _
      (fun s => fakeKernel scheme s.1.1 s.1.2.1.2.1 s.2)
      (fun _ s => fakeInvariant s.1.1 s.1.2.1.2.1 s.2) ?_ ?_ ?_ ?_ <;>
    dsimp only [𝓜.freshSampling, 𝓒.freshSampling, MAC.SUF.freshSamplingReal, MAC.Real.freshSampling,
      Encryption.Left.freshSamplingReal, Encryption.Right.freshSamplingReal,
      Encryption.Real.freshSampling, FreshSampling.ofRightContext, FreshSampling.cast,
      FreshSampling.ofPreservingProgram, FreshSampling.ofProgram, FreshSampling.parallel,
      FreshSampling.source, id, Distribution.ProbDist.single, Distribution.ProbDist.map]
    · rintro s hs
      rw [fTransform_single] at hs
      obtain rfl := ((Finsupp.mem_support_single _ _ _).mp hs).1
      exact ⟨rfl, rfl⟩
    · rintro xs ⟨⟨k, r, ⟨⟩, ⟨⟩⟩, D⟩ x - - p hp
      rw [ProbStep.outcome_withRecord, ProbStep.outcome] at hp
      obtain ⟨p', hp', rfl⟩ := mem_support_fTransform _ _ hp
      obtain ⟨p'', hp'', rfl⟩ := mem_support_fTransform _ _ hp'
      obtain ⟨km, hkm⟩ := 𝓒.mem_support_step mac hp''
      show fakeInvariant p''.1.1 _ _
      rw [hkm]
      trivial
    · rintro xs ⟨⟨k, ⟨l, e, ⟨⟩, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩, D⟩ ⟨_ | _, x⟩ hinv -
      · obtain ⟨mL, mR⟩ := x
        unfold ProbStep.SimulatesAt
        conv_rhs => rw [ProbStep.outcome_withRecord, ProbStep.outcome]
        first
          | rw [𝓒.step_enc mac (Encryption.Left.step_enc (Encryption.Real.step_enc scheme _ mL))]
          | rw [𝓒.step_enc mac (Encryption.Right.step_enc (Encryption.Real.step_enc scheme _ mR))]
        rcases k with _ | km <;> rcases e with _ | ke
        · obtain ⟨-, rfl⟩ := hinv
          simp only [fakeKernel, Distribution.ProbDist.single, bindK_single, one_smul]
          rw [ProbStep.outcome,
            𝓜.step_enc scheme _ (fun c => MAC.SUF.step_tag (MAC.Real.step_tag mac _ c))]
          simp only [keyLaw, bindK_bindK, bindK_fTransform, fTransform_bindK, fTransform_fTransform,
            Function.comp_def, ProbStep.tagged, challengesAfter, Distribution.ProbDist.map,
            fTransform_single, bindK_single_comp, Option.getD_none, Option.map_none,
            Bool.false_eq_true, ↓reduceIte]
          conv_rhs => rw [bindK_comm]
          refine bindK_congr fun ke _ => ?_
          rw [bindK_comm]
        · obtain ⟨h, -⟩ := hinv
          exact absurd h (by simp)
        · simp only [fakeKernel, Distribution.ProbDist.map, bindK_fTransform, Function.comp_def]
          conv_lhs => enter [2, ke]; rw [ProbStep.outcome,
            𝓜.step_enc scheme _ (fun c => MAC.SUF.step_tag (MAC.Real.step_tag mac _ c))]
          simp only [keyLaw, bindK_bindK, bindK_fTransform, fTransform_bindK, fTransform_fTransform,
            Function.comp_def, ProbStep.tagged, challengesAfter, Distribution.ProbDist.single,
            fTransform_single, bindK_single, one_smul, bindK_single_comp, Option.getD_some,
            Option.map_some, Bool.false_eq_true, ↓reduceIte]
        · simp only [fakeKernel, Distribution.ProbDist.single, bindK_single, one_smul]
          rw [ProbStep.outcome,
            𝓜.step_enc scheme _ (fun c => MAC.SUF.step_tag (MAC.Real.step_tag mac _ c))]
          simp only [keyLaw, bindK_bindK, bindK_fTransform, fTransform_bindK, fTransform_fTransform,
            Function.comp_def, ProbStep.tagged, challengesAfter, Distribution.ProbDist.map,
            fTransform_single, bindK_single, one_smul, bindK_single_comp, Option.getD_some,
            Option.map_some, Bool.false_eq_true, ↓reduceIte]
      · obtain ⟨c, t⟩ := x
        unfold ProbStep.SimulatesAt
        conv_rhs => rw [ProbStep.outcome_withRecord, ProbStep.outcome, 𝓒.step_dec mac (c, t)]
        rcases k with _ | km <;> rcases e with _ | ke
        · obtain ⟨-, rfl⟩ := hinv
          simp only [fakeKernel, Distribution.ProbDist.single, bindK_single, one_smul]
          rw [ProbStep.outcome,
            𝓜.step_dec scheme _ (MAC.SUF.step_verify (MAC.Real.step_verify mac _ c t))]
          simp only [keyLaw, bindK_fTransform, fTransform_bindK, fTransform_fTransform,
            Function.comp_def, ProbStep.tagged, challengesAfter, Distribution.ProbDist.map,
            bindK_single_comp, Option.getD_none, Option.map_none, List.not_mem_nil, decide_false,
            Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact bindK_fTransform_comm _ _ _
        · obtain ⟨h, -⟩ := hinv
          exact absurd h (by simp)
        · simp only [fakeKernel, Distribution.ProbDist.map, bindK_fTransform, Function.comp_def]
          conv_lhs => enter [2, ke]; rw [ProbStep.outcome,
            𝓜.step_dec scheme _ (MAC.SUF.step_verify (MAC.Real.step_verify mac _ c t))]
          by_cases hc : (c, t) ∈ D <;>
          simp only [keyLaw, fTransform_fTransform, Function.comp_def, ProbStep.tagged,
            challengesAfter, Distribution.ProbDist.single, fTransform_single, bindK_single,
            one_smul, bindK_single_comp, Option.getD_some, Option.map_some, hc, decide_false,
            Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        · simp only [fakeKernel, Distribution.ProbDist.single, bindK_single, one_smul]
          rw [ProbStep.outcome,
            𝓜.step_dec scheme _ (MAC.SUF.step_verify (MAC.Real.step_verify mac _ c t))]
          by_cases hc : (c, t) ∈ D <;>
          simp only [keyLaw, ProbStep.tagged, challengesAfter, Distribution.ProbDist.map,
            fTransform_single, bindK_single, one_smul, bindK_single_comp, Option.getD_some,
            Option.map_some, hc, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    · rw [fTransform_single, bindK_single, one_smul]
      rfl

end FreshSampling

omit [DecidableEq T] in
/-- **Encrypt-then-MAC is IND-CPA** [1]: if `Σ_e` is IND-CPA within `ε`, then encrypt-then-MAC
is IND-CPA within `ε` at the distinguishers with `π_enc` absorbed, the MAC beside the
encryption. -/
theorem encrypt_then_mac_ind_cpa [AdmissibleDistinguishers] [Nonempty M]
    (scheme : SymmetricEncryption Ke M C) (mac : MAC Km C T) {q : Encryption.Port → ℕ}
    (ε : (Encryption.perPort M C q).inputDomain.DistinguisherBehavior → ENNReal)
    (cpa : Encryption.INDCPA scheme ε) :
    Encryption.INDCPA (EncryptThenMAC scheme mac) fun D =>
      ε (absorb (𝓟ₑ.perLabel q ≫ Interface.rightContext _ (MAC.Real.perPort mac)) D) := by
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    Encryption.Real.perPort (EncryptThenMAC scheme mac) =
        𝓟ₑ.perLabel q • (Encryption.Real.perPort scheme ∥ MAC.Real.perPort mac) :=
      encryptionReal_eq scheme mac q
    _ = (𝓟ₑ.perLabel q ≫ Interface.rightContext _ (MAC.Real.perPort mac)) •
        Encryption.Real.perPort scheme := by
      rw [Interface.comp_smul, Interface.attach_rightContext]
    _ ≃[ε ∘ absorb (𝓟ₑ.perLabel q ≫ Interface.rightContext _ (MAC.Real.perPort mac))]
        (𝓟ₑ.perLabel q ≫ Interface.rightContext _ (MAC.Real.perPort mac)) •
          ρ^cpa • Encryption.Real.perPort scheme :=
      AdmissibleDistinguishers.substitutesWithin_attach _ cpa
    _ = 𝓟ₑ.perLabel q • (ρ^cpa • Encryption.Real.perPort scheme ∥ MAC.Real.perPort mac) := by
      rw [Interface.comp_smul, Interface.attach_rightContext]
    _ = ρ^cpa • (𝓟ₑ.perLabel q •
        (Encryption.Real.perPort scheme ∥ MAC.Real.perPort mac)) := cpa_comm scheme mac q
    _ = ρ^cpa • Encryption.Real.perPort (EncryptThenMAC scheme mac) := by
      rw [encryptionReal_eq scheme mac q]

/-- **Encrypt-then-MAC is INT-CTXT** [1]: if `Σ_m` is SUF-CMA within `ε` and both schemes are
correct, then encrypt-then-MAC is INT-CTXT within `ε` at the distinguishers with `π_EtM`
absorbed, `⟦E_k, D_k⟧` of `Σ_e` beside the MAC. -/
theorem encrypt_then_mac_int_ctxt [AdmissibleDistinguishers]
    (scheme : SymmetricEncryption Ke M C) (mac : MAC Km C T)
    (schemeCorrect : scheme.Correct) (macCorrect : mac.Correct) {q : AE.Port → ℕ}
    (ε : (Tagging.perPort C T (tagBudget q)).inputDomain.DistinguisherBehavior → ENNReal)
    (suf : MAC.SUFCMA mac ε) :
    AE.INTCTXT (EncryptThenMAC scheme mac) fun D =>
      ε (absorb (𝓟.perLabel q ≫ Interface.leftContext (AE.Real.perPort scheme) _) D) := by
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    AE.Real.perPort (EncryptThenMAC scheme mac) =
        𝓟.perLabel q • (AE.Real.perPort scheme ∥ MAC.Real.perPort mac) := real_eq scheme mac q
    _ = (𝓟.perLabel q ≫ Interface.leftContext (AE.Real.perPort scheme) _) •
        MAC.Real.perPort mac := by
      rw [Interface.comp_smul, Interface.attach_leftContext]
    _ ≃[ε ∘ absorb (𝓟.perLabel q ≫ Interface.leftContext (AE.Real.perPort scheme) _)]
        (𝓟.perLabel q ≫ Interface.leftContext (AE.Real.perPort scheme) _) •
          MAC.SUF.perPort C T • MAC.Real.perPort mac :=
      AdmissibleDistinguishers.substitutesWithin_attach _ suf
    _ = 𝓟.perLabel q • (AE.Real.perPort scheme ∥ MAC.SUF.perPort C T • MAC.Real.perPort mac) := by
      rw [Interface.comp_smul, Interface.attach_leftContext]
    _ = ρ^ctxt • Encryption.Real.perPort (EncryptThenMAC scheme mac) :=
      suf_eq_ctxt scheme mac schemeCorrect macCorrect q

/-- **Encrypt-then-MAC is ae**: SUF-CMA of `Σ_m` within `εmac` and IND-CPA of `Σ_e` within `εcpa`
give ae within the two losses, through `(ind-cpa, int-ctxt) → ae`. -/
theorem encrypt_then_mac_ae [AdmissibleDistinguishers] [Nonempty M]
    (scheme : SymmetricEncryption Ke M C) (mac : MAC Km C T)
    (schemeCorrect : scheme.Correct) (macCorrect : mac.Correct) {q : AE.Port → ℕ}
    (εmac : (Tagging.perPort C T (tagBudget q)).inputDomain.DistinguisherBehavior → ENNReal)
    (εcpa : (Encryption.perPort M C
      (AE.CTXT.insideBudget M (C × T) q)).inputDomain.DistinguisherBehavior → ENNReal)
    (suf : MAC.SUFCMA mac εmac) (cpa : Encryption.INDCPA scheme εcpa) :
    AE.Secure (EncryptThenMAC scheme mac) fun D =>
      εmac (absorb (𝓟.perLabel q ≫ Interface.leftContext (AE.Real.perPort scheme) _) D) +
        εcpa (absorb (𝓟ₑ.perLabel (AE.CTXT.insideBudget M (C × T) q) ≫
          Interface.rightContext _ (MAC.Real.perPort mac)) (absorb ρ^ctxt D)) :=
  ae_of_ind_cpa_int_ctxt _ _ _
    (encrypt_then_mac_int_ctxt scheme mac schemeCorrect macCorrect εmac suf)
    (encrypt_then_mac_ind_cpa scheme mac εcpa cpa)

/-- **`π_EtM` constructs authenticated encryption** from the two schemes: attached to
`⟦E_k, D_k⟧ ∥ ⟦S_k, V_k⟧` of `Σ_e` and `Σ_m`, it substitutes for the ideal `ρ^ae(E_k)` of
encrypt-then-MAC within the losses of `encrypt_then_mac_ae`, in Jost's reduction relaxation. -/
theorem encrypt_then_mac_constructs [AdmissibleDistinguishers] [Nonempty M]
    (scheme : SymmetricEncryption Ke M C) (mac : MAC Km C T)
    (schemeCorrect : scheme.Correct) (macCorrect : mac.Correct) {q : AE.Port → ℕ}
    (εmac : (Tagging.perPort C T (tagBudget q)).inputDomain.DistinguisherBehavior → ENNReal)
    (εcpa : (Encryption.perPort M C
      (AE.CTXT.insideBudget M (C × T) q)).inputDomain.DistinguisherBehavior → ENNReal)
    (suf : MAC.SUFCMA mac εmac) (cpa : Encryption.INDCPA scheme εcpa) :
    Specification.Constructs (𝓟.perLabel q) {AE.Real.perPort scheme ∥ MAC.Real.perPort mac}
      (Specification.reductionRelaxation
        (Interface.distinguisherAdvantage AdmissibleDistinguishers.admissible)
        (fun D =>
          εmac (absorb (𝓟.perLabel q ≫ Interface.leftContext (AE.Real.perPort scheme) _) D) +
            εcpa (absorb (𝓟ₑ.perLabel (AE.CTXT.insideBudget M (C × T) q) ≫
              Interface.rightContext _ (MAC.Real.perPort mac)) (absorb ρ^ctxt D)))
        {(ρ^ae • Encryption.Real.perPort (EncryptThenMAC scheme mac) :
          Resource (AE.perPort M (C × T) q))}) := by
  rw [Specification.constructs_singleton_reductionRelaxation_iff]
  have ae := encrypt_then_mac_ae scheme mac schemeCorrect macCorrect εmac εcpa suf cpa
  rw [AE.Secure, AE.Secure.systems, real_eq scheme mac q] at ae
  exact ae

/-- **Encrypt-then-MAC is CCA-secure** [4, §5]: if `Σ_e` is left-or-right CPA-secure within
`εcpa` and `Σ_m` is SUF-CMA within `εmac`, then encrypt-then-MAC is left-or-right CCA-secure
within the losses of the three swaps. -/
theorem encrypt_then_mac_cca [AdmissibleDistinguishers]
    (scheme : SymmetricEncryption Ke M C) (mac : MAC Km C T) {q : LeftRightCCA.Port → ℕ}
    (εmac : (Tagging.perPort C T
      (𝓜.insideBudget T scheme false q)).inputDomain.DistinguisherBehavior → ENNReal)
    (εcpa : (LeftRight.perPort M C (𝓒.insideBudget M C mac q)).inputDomain.DistinguisherBehavior →
      ENNReal)
    (suf : MAC.SUFCMA mac εmac)
    (cpa : Encryption.Left.perPort M C • Encryption.Real.perPort scheme ≃[εcpa]
      Encryption.Right.perPort M C • Encryption.Real.perPort scheme) :
    Encryption.LORCCA (EncryptThenMAC scheme mac) fun D =>
      εmac (absorb (𝓜.perPort T scheme false) D) + εcpa (absorb (𝓒.perPort M C mac) D) +
        εmac (absorb (𝓜.perPort T scheme true) D) := by
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    (Encryption.LORCCA.systems (EncryptThenMAC scheme mac) q).1 =
        𝓜.perPort T scheme false • MAC.Real.perPort mac := cca_eq scheme mac q false
    _ ≃[εmac ∘ absorb (𝓜.perPort T scheme false)]
        𝓜.perPort T scheme false • MAC.SUF.perPort C T • MAC.Real.perPort mac :=
      AdmissibleDistinguishers.substitutesWithin_attach _ suf
    _ = 𝓒.perPort M C mac • Encryption.Left.perPort M C • Encryption.Real.perPort scheme :=
      fake_eq scheme mac q false
    _ ≃[εcpa ∘ absorb (𝓒.perPort M C mac)]
        𝓒.perPort M C mac • Encryption.Right.perPort M C • Encryption.Real.perPort scheme :=
      AdmissibleDistinguishers.substitutesWithin_attach _ cpa
    _ = 𝓜.perPort T scheme true • MAC.SUF.perPort C T • MAC.Real.perPort mac :=
      (fake_eq scheme mac q true).symm
    _ ≃[εmac ∘ absorb (𝓜.perPort T scheme true)] 𝓜.perPort T scheme true • MAC.Real.perPort mac :=
      AdmissibleDistinguishers.substitutesWithin_attach _
        (DistinguisherAdvantage.SubstitutesWithin.symm _ suf)
    _ = (Encryption.LORCCA.systems (EncryptThenMAC scheme mac) q).2 :=
      (cca_eq scheme mac q true).symm

end

end ProofLadders.EtM
