import Commons.Definitions.AEAD

/-!
# Symmetric encryption notions of the ladder

Notions of the ladder's encryption problems that Commons lacks, in the form of the Commons
notions: a notion is the pair of its systems, each a converter applied to the scheme's own real
system, and the predicate of the same name states it for the admitted distinguishers,
`X₀ ≃[ε] X₁`.

* Correctness of a symmetric-key encryption scheme: decryption recovers every encryption.
* Left-or-right CCA security [1, §5]: `cca-left` encrypts the left message of each pair and
  `cca-right` the right one, both recording their ciphertexts in `𝒟` and answering `⊥` to the
  decryption of a recorded ciphertext. Both are transformations of the correlated oracles
  `⟦E_k, D_k⟧` of `AE.Real`.
* One-time security of a DEM [3]: `Left` and `Right` of Commons, which encrypt the left and the
  right message of each pair, on the one-time encryption system, which encrypts each message
  under a fresh key. The keys are uniform, `k ←$ K`.
* Single-challenge CCA security of a DEM [2, Definition 3]: the challenge converter for the bit
  `b` on `⟦E_k, D_k⟧` for a uniform key `k ←$ K`. It encrypts `m_b` at the first challenge,
  answers `⊥` to the later ones, and refuses to decrypt the challenge ciphertext.

Upstream candidates: `SymmetricEncryption.Correct` for `Commons.Definitions.Encryption`;
`LeftRightCCA`, `Encryption.LeftCCA`, `Encryption.RightCCA`, `Encryption.LORCCA.systems` and
`Encryption.LORCCA` for `Commons.Definitions.AEAD`; `Encryption.OneTime`,
`Encryption.OTS.systems`, `Encryption.OTS`, `ChallengeLeftRight`, `DEM.ChallengeCCA.Challenge`,
`DEM.ChallengeCCA.systems` and `DEM.ChallengeCCA` for `Commons.Definitions.Encryption`.

## Main definitions

* `SymmetricEncryption.Correct`: correctness
* `LeftRightCCA M C`, `Encryption.LORCCA.systems`, `Encryption.LORCCA`: left-or-right CCA
* `Encryption.OneTime scheme`: the one-time encryption system
* `Encryption.OTS.systems`, `Encryption.OTS`: one-time security
* `ChallengeLeftRight M C`, `DEM.ChallengeCCA.Challenge M C b`: the interface and the challenge
  converter of single-challenge CCA security of a DEM
* `DEM.ChallengeCCA.systems`, `DEM.ChallengeCCA`: single-challenge CCA security of a DEM

## References

1. The symmetric proof ladder, *Security proofs in the style of The Joy of Cryptography*,
   `proof-ladders/symmetric-ladder`, `Notes/selfcontained.tex`.
2. M. Barbosa. *Yet another set of HACS examples*. The asymmetric proof ladder,
   `proof-ladders/asymmetric-ladder`, `asymmetric-problems.pdf`, 2025.
3. The asymmetric proof ladder, KEM-DEM in ProofFrog, `kemdem/ProofFrog/src/SymEnc-OTS.game`.
-/

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

/-- **Correctness** of a symmetric-key encryption scheme: for every generated key, decryption
recovers the message of each of its encryptions. -/
def SymmetricEncryption.Correct {K M C : Type} (scheme : SymmetricEncryption K M C) : Prop :=
  ∀ k, k ∈ scheme.gen.1.support → ∀ m c, c ∈ (scheme.enc k m).1.support → scheme.dec k c = some m

interface LeftRightCCA(M C : Type) [Fintype M] [Fintype C]
  enc(left : M, right : M) → C
  dec(ciphertext : C) → Option M

interface ChallengeLeftRight(M C : Type) [Fintype M] [Fintype C]
  challenge(left : M, right : M) → Option C
  dec(ciphertext : C) → Option M

noncomputable section

/-! ## Left-or-right CCA security -/

-- `cca-left`: on `(m_L, m_R)`, encrypt `m_L` and add the ciphertext to `𝒟`; on `c`, output `⊥`
-- if `c ∈ 𝒟`, otherwise decrypt `c`.
converter Encryption.LeftCCA(M C : Type) [Fintype M] [Fintype C] [DecidableEq C] : LeftRightCCA M C
  inside ae : AE M C
  initialize
    challenges ← ([] : List C)
  on enc(left : M, _right : M) → C
    c ← ae.enc(left)
    challenges ← challenges ++ [c]
    return c
  on dec(ciphertext : C) → Option M
    if decide (ciphertext ∈ challenges)
      return none
    else
      m ← ae.dec(ciphertext)
      return m

-- `cca-right`: on `(m_L, m_R)`, encrypt `m_R` and add the ciphertext to `𝒟`; on `c`, output `⊥`
-- if `c ∈ 𝒟`, otherwise decrypt `c`.
converter Encryption.RightCCA(M C : Type) [Fintype M] [Fintype C] [DecidableEq C] : LeftRightCCA M C
  inside ae : AE M C
  initialize
    challenges ← ([] : List C)
  on enc(_left : M, right : M) → C
    c ← ae.enc(right)
    challenges ← challenges ++ [c]
    return c
  on dec(ciphertext : C) → Option M
    if decide (ciphertext ∈ challenges)
      return none
    else
      m ← ae.dec(ciphertext)
      return m

-- The challenge of `IND-CCA^DEM(b)` [2, Figure 1] on `⟦E_k, D_k⟧`: the first `(m₀, m₁)` gets
-- `c* ← E_k(m_b)`; on `c`, output `⊥` if `c = c*`, otherwise `D_k(c)`.
converter DEM.ChallengeCCA.Challenge(M C : Type) [Fintype M] [Fintype C] [DecidableEq C] (b : Bool) : ChallengeLeftRight M C
  inside ae : AE M C
  initialize
    cstar ← (none : Option C)
  on challenge(m₀ : M, m₁ : M) → Option C
    match cstar
    | some _ →
      return none
    | none →
      c ← ae.enc(if b then m₁ else m₀)
      cstar ← some c
      return cstar
  on dec(c : C) → Option M
    if cstar = some c
      return none
    else
      m ← ae.dec(c)
      return m

variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C]

/-- **The systems of left-or-right CCA security** [1, §5]: `cca-left` and `cca-right`, the
transformations of `⟦E_k, D_k⟧` for `k ← Gen`, at the budget `q` per port. -/
def Encryption.LORCCA.systems [DecidableEq K] [DecidableEq M] [DecidableEq C]
    (scheme : SymmetricEncryption K M C) (q : LeftRightCCA.Port → ℕ) :
    Interface.Resource (LeftRightCCA.perPort M C q) ×
      Interface.Resource (LeftRightCCA.perPort M C q) :=
  (Encryption.LeftCCA.perPort M C • AE.Real.perPort scheme,
    Encryption.RightCCA.perPort M C • AE.Real.perPort scheme)

/-- **Left-or-right CCA security** within `error`: against the admitted distinguishers,
`cca-left` substitutes for `cca-right`. -/
def Encryption.LORCCA [Interface.AdmissibleDistinguishers] [DecidableEq K] [DecidableEq M]
    [DecidableEq C] (scheme : SymmetricEncryption K M C) {q : LeftRightCCA.Port → ℕ}
    (error : (LeftRightCCA.perPort M C q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (Encryption.LORCCA.systems scheme q).1 ≃[error] (Encryption.LORCCA.systems scheme q).2

/-! ## One-time security -/

-- The one-time encryption system: on `m`, output `Enc(k, m)` for a fresh `k ← Gen`.
system Encryption.OneTime(scheme : SymmetricEncryption K M C) [DecidableEq K] [DecidableEq M] : Encryption M C
  on enc(message : M) → C
    key ←$ scheme.gen
    encryptions ←$ scheme.encryptions
    return encryptions (key, message)

/-- **The systems of one-time security** [3]: `Left` and `Right` on the one-time encryption
system of the scheme with uniform keys `k ←$ K`, at the budget `q` per port. -/
def Encryption.OTS.systems [Nonempty K] [DecidableEq K] [DecidableEq M]
    (scheme : SymmetricEncryption K M C) (q : LeftRight.Port → ℕ) :
    Interface.Resource (LeftRight.perPort M C q) × Interface.Resource (LeftRight.perPort M C q) :=
  (Encryption.Left.perPort M C • Encryption.OneTime.perPort { scheme with gen := 𝒰[K] },
    Encryption.Right.perPort M C • Encryption.OneTime.perPort { scheme with gen := 𝒰[K] })

/-- **One-time security** within `error`: against the admitted distinguishers, encrypting the
left messages under fresh keys substitutes for encrypting the right ones. -/
def Encryption.OTS [Interface.AdmissibleDistinguishers] [Nonempty K] [DecidableEq K]
    [DecidableEq M] (scheme : SymmetricEncryption K M C) {q : LeftRight.Port → ℕ}
    (error : (LeftRight.perPort M C q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (Encryption.OTS.systems scheme q).1 ≃[error] (Encryption.OTS.systems scheme q).2

/-! ## Single-challenge CCA security of a DEM -/

/-- **The systems of single-challenge CCA security of a DEM** [2, Definition 3]: the challenge
for the bits `0` and `1` on `⟦E_k, D_k⟧` for a uniform key `k ←$ K`, at a total budget of `q`
queries. -/
def DEM.ChallengeCCA.systems [Nonempty K] [DecidableEq K] [DecidableEq M] [DecidableEq C]
    (scheme : SymmetricEncryption K M C) (q : ℕ) :
    Interface.Resource (ChallengeLeftRight M C q) ×
      Interface.Resource (ChallengeLeftRight M C q) :=
  (DEM.ChallengeCCA.Challenge M C false • AE.Real { scheme with gen := 𝒰[K] },
    DEM.ChallengeCCA.Challenge M C true • AE.Real { scheme with gen := 𝒰[K] })

/-- **Single-challenge CCA security of a DEM** within `error`: against the admitted
distinguishers, the challenge for the bit `0` substitutes for the challenge for the bit `1`. -/
def DEM.ChallengeCCA [Interface.AdmissibleDistinguishers] [Nonempty K] [DecidableEq K]
    [DecidableEq M] [DecidableEq C] (scheme : SymmetricEncryption K M C) {q : ℕ}
    (error : (ChallengeLeftRight M C q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (DEM.ChallengeCCA.systems scheme q).1 ≃[error] (DEM.ChallengeCCA.systems scheme q).2

end

end Commons
