import Commons.Definitions.KEM
import Commons.Definitions.PublicKeyEncryption
import ProofLadders.Common.Encryption
import ProofLadders.Common.Probability
import ProofLadders.Common.Programs

/-!
# Public-key notions of the ladder

Notions of the KEM-DEM problem [1] that Commons lacks, in the form of the Commons notions: a
notion is the pair of its systems, each a converter applied to the scheme's own real system, and
the predicate of the same name states it for the admitted distinguishers, `X₀ ≃[ε] X₁`.

* Left-or-right CPA security of a PKE [2]: the converters `Left` and `Right`, which publish the
  public key and encrypt the left, or the right, message of each pair, on the public key, `E_pk`
  and `D_sk` of `PKE.Real`, at per-label inside budgets with no decryption.
* Single-challenge CCA security of a PKE and of a KEM [1, Definitions 1–2]: the challenge
  converters for the bit `b` on `PKE.Real` and on `KEM.Real`. The PKE challenge encrypts `m_b` at
  the first challenge, answers `⊥` to the later ones, and refuses to decrypt the challenge
  ciphertext. The KEM challenge encapsulates once, at the first query, and gives the public key,
  the challenge ciphertext and the encapsulated or a uniform key; it refuses to decapsulate the
  challenge ciphertext.
* The correctness error of a KEM: the probability that decapsulation misses the encapsulated key.

Upstream candidates: `PKELeftRight`, `PKE.Left`, `PKE.Right`, `PKE.LORCPA.insideBudget`,
`PKE.LORCPA.insideCalls`, `PKE.Left.labelBounded`, `PKE.Right.labelBounded`,
`PKE.LORCPA.admits`, `PKE.Left.perLabel`, `PKE.Right.perLabel`, `PKE.LORCPA.systems`,
`PKE.LORCPA`, `PKEChallenge`, `PKE.ChallengeCCA.Challenge`, `PKE.ChallengeCCA.systems` and
`PKE.ChallengeCCA` for `Commons.Definitions.PublicKeyEncryption`; `KEMChallenge`,
`KEM.ChallengeCCA.Challenge`, `KEM.ChallengeCCA.systems`, `KEM.ChallengeCCA` and
`KEM.CorrectnessError` for `Commons.Definitions.KEM`.

## Main definitions

* `PKELeftRight PK M C`, `PKE.Left`, `PKE.Right`: the interface of message pairs with the public
  key, and the encryption of the left and of the right message
* `PKE.Left.perLabel`, `PKE.Right.perLabel`: `Left` and `Right` at per-label inside budgets
* `PKE.LORCPA.systems`, `PKE.LORCPA`: left-or-right CPA security
* `PKEChallenge PK M C`, `PKE.ChallengeCCA.Challenge PK M C b`, `PKE.ChallengeCCA`: the
  interface, the challenge converter and single-challenge CCA security of a PKE
* `KEMChallenge PK C K`, `KEM.ChallengeCCA.Challenge PK C K b`, `KEM.ChallengeCCA`: the same for
  a KEM
* `KEM.CorrectnessError kem δ`: the correctness error of a KEM is at most `δ`

## References

1. M. Barbosa. *Yet another set of HACS examples*. The asymmetric proof ladder,
   `proof-ladders/asymmetric-ladder`, `asymmetric-problems.pdf`, 2025.
2. The asymmetric proof ladder, KEM-DEM in ProofFrog, `kemdem/ProofFrog/src/PKE-CPA.game`.
-/

namespace Commons

open SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface Probability
open scoped SystemAlgebra SystemAlgebra.DSL

interface PKELeftRight(PK M C : Type) [Fintype PK] [Fintype M] [Fintype C]
  publicKey() → PK
  enc(left : M, right : M) → C

interface PKEChallenge(PK M C : Type) [Fintype PK] [Fintype M] [Fintype C]
  publicKey() → PK
  challenge(m₀ : M, m₁ : M) → Option C
  dec(c : C) → Option M

interface KEMChallenge(PK C K : Type) [Fintype PK] [Fintype C] [Fintype K]
  input() → PK × C × K
  dec(c : C) → Option K

noncomputable section

/-! ## Left-or-right CPA security of a PKE -/

-- `Left` [2] on the public key and `E_pk`: publish `pk`; on `(m_L, m_R)`, output `E(pk, m_L)`.
converter PKE.Left(PK M C : Type) [Fintype PK] [Fintype M] [Fintype C] : PKELeftRight PK M C
  inside pke : PKE PK M C
  on publicKey() → PK
    pk ← pke.publicKey()
    return pk
  on enc(left : M, _right : M) → C
    ciphertext ← pke.enc(left)
    return ciphertext

-- `Right` [2] on the public key and `E_pk`: publish `pk`; on `(m_L, m_R)`, output `E(pk, m_R)`.
converter PKE.Right(PK M C : Type) [Fintype PK] [Fintype M] [Fintype C] : PKELeftRight PK M C
  inside pke : PKE PK M C
  on publicKey() → PK
    pk ← pke.publicKey()
    return pk
  on enc(_left : M, right : M) → C
    ciphertext ← pke.enc(right)
    return ciphertext

/-- The PKE budget of `Left` and `Right`: the public key per public-key query, an encryption per
pair, and no decryption. -/
abbrev PKE.LORCPA.insideBudget (q : PKELeftRight.Port → ℕ) : PKE.Port → ℕ
  | .publicKey => q .publicKey
  | .enc => q .enc
  | .dec => 0

/-- The inside calls of `Left` and `Right` per procedure: the public key from `publicKey`, an
encryption from `enc`. -/
def PKE.LORCPA.insideCalls : PKELeftRight.Port → PKE.Port → ℕ
  | .publicKey, .publicKey => 1
  | .enc, .enc => 1
  | _, _ => 0

variable {PK SK M C K : Type} [Fintype PK] [Fintype SK] [Fintype M] [Fintype C] [Fintype K]

/-- `Left` calls each inside label at most `PKE.LORCPA.insideCalls` times per procedure. -/
lemma PKE.Left.labelBounded :
    (PKE.Left.body PK M C).LabelBounded PKE.LORCPA.insideCalls := by
  intro s o u
  cases o <;> simp only [PKE.Left.body] <;> cases s <;> dsimp only <;>
    repeat' (first
      | exact Program.labelCallBound_return _ _
      | (refine Program.labelCallBound_call _ _ _ (by decide) fun y => ?_))

/-- `Right` calls each inside label at most `PKE.LORCPA.insideCalls` times per procedure. -/
lemma PKE.Right.labelBounded :
    (PKE.Right.body PK M C).LabelBounded PKE.LORCPA.insideCalls := by
  intro s o u
  cases o <;> simp only [PKE.Right.body] <;> cases s <;> dsimp only <;>
    repeat' (first
      | exact Program.labelCallBound_return _ _
      | (refine Program.labelCallBound_call _ _ _ (by decide) fun y => ?_))

/-- The PKE at the budget of `Left` and `Right` admits their per-label budget. -/
lemma PKE.LORCPA.admits (q : PKELeftRight.Port → ℕ) :
    (PKE.perPort PK M C (PKE.LORCPA.insideBudget q)).AdmitsLabelBudget
      fun j => ∑ o, PKE.LORCPA.insideCalls o j * q o := by
  refine (portBudget_admitsLabelBudget _ _ _ _).mono fun j => ?_
  cases j <;> simp [Finset.univ, Fintype.elems, PKE.LORCPA.insideCalls]

/-- **`Left` at per-port budgets**: the program of `Left` at the per-label call bound
`PKE.LORCPA.insideCalls`, into the PKE without decryption queries. -/
def PKE.Left.perLabel (PK M C : Type) [Fintype PK] [Fintype M] [Fintype C]
    (q : PKELeftRight.Port → ℕ) :
    PKELeftRight.perPort PK M C q ⟶ PKE.perPort PK M C (PKE.LORCPA.insideBudget q) :=
  Converter.ofLabelBoundedProgram (A := PKELeftRight.perPort PK M C q) none (PKE.Left.body PK M C)
    (PKE.Left.bound_spec PK M C) PKE.LORCPA.insideCalls PKE.Left.labelBounded q
    (fun _ hd => hd.2) (PKE.LORCPA.admits q)

/-- **`Right` at per-port budgets**: the program of `Right` at the per-label call bound
`PKE.LORCPA.insideCalls`, into the PKE without decryption queries. -/
def PKE.Right.perLabel (PK M C : Type) [Fintype PK] [Fintype M] [Fintype C]
    (q : PKELeftRight.Port → ℕ) :
    PKELeftRight.perPort PK M C q ⟶ PKE.perPort PK M C (PKE.LORCPA.insideBudget q) :=
  Converter.ofLabelBoundedProgram (A := PKELeftRight.perPort PK M C q) none
    (PKE.Right.body PK M C) (PKE.Right.bound_spec PK M C) PKE.LORCPA.insideCalls
    PKE.Right.labelBounded q (fun _ hd => hd.2) (PKE.LORCPA.admits q)

/-- **The systems of left-or-right CPA security** [2]: `Left` and `Right` on the public key,
`E_pk` and `D_sk` for `(pk, sk) ← G`, at the budget `q` per port. -/
def PKE.LORCPA.systems [DecidableEq PK] [DecidableEq M]
    (scheme : PublicKeyEncryption PK SK M C) (q : PKELeftRight.Port → ℕ) :
    Interface.Resource (PKELeftRight.perPort PK M C q) ×
      Interface.Resource (PKELeftRight.perPort PK M C q) :=
  (PKE.Left.perLabel PK M C q • PKE.Real.perPort scheme,
    PKE.Right.perLabel PK M C q • PKE.Real.perPort scheme)

/-- **Left-or-right CPA security** within `error`: against the admitted distinguishers,
encrypting the left messages substitutes for encrypting the right ones. -/
def PKE.LORCPA [Interface.AdmissibleDistinguishers] [DecidableEq PK] [DecidableEq M]
    (scheme : PublicKeyEncryption PK SK M C) {q : PKELeftRight.Port → ℕ}
    (error : (PKELeftRight.perPort PK M C q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (PKE.LORCPA.systems scheme q).1 ≃[error] (PKE.LORCPA.systems scheme q).2

/-! ## Single-challenge CCA security of a PKE -/

-- The challenge of `IND-CCA^PKE(b)` [1, Figure 1] on the public key, `E_pk` and `D_sk`: publish
-- `pk`; the first `(m₀, m₁)` gets `c* ← E(pk, m_b)`; on `c`, output `⊥` if `c = c*`, otherwise
-- `D(sk, c)`.
converter PKE.ChallengeCCA.Challenge(PK M C : Type) [Fintype PK] [Fintype M] [Fintype C] [DecidableEq C] (b : Bool) : PKEChallenge PK M C
  inside pke : PKE PK M C
  initialize
    cstar ← (none : Option C)
  on publicKey() → PK
    pk ← pke.publicKey()
    return pk
  on challenge(m₀ : M, m₁ : M) → Option C
    match cstar
    | some _ →
      return none
    | none →
      c ← pke.enc(if b then m₁ else m₀)
      cstar ← some c
      return cstar
  on dec(c : C) → Option M
    if cstar = some c
      return none
    else
      m ← pke.dec(c)
      return m

/-- **The systems of single-challenge CCA security of a PKE** [1, Definition 1]: the challenge
for the bits `0` and `1` on the public key, `E_pk` and `D_sk` for `(pk, sk) ← Gen`, at a total
budget of `q` queries. -/
def PKE.ChallengeCCA.systems [DecidableEq PK] [DecidableEq M] [DecidableEq C]
    (scheme : PublicKeyEncryption PK SK M C) (q : ℕ) :
    Interface.Resource (PKEChallenge PK M C q) × Interface.Resource (PKEChallenge PK M C q) :=
  (PKE.ChallengeCCA.Challenge PK M C false • PKE.Real scheme,
    PKE.ChallengeCCA.Challenge PK M C true • PKE.Real scheme)

/-- **Single-challenge CCA security of a PKE** within `error`: against the admitted
distinguishers, the challenge for the bit `0` substitutes for the challenge for the bit `1`. -/
def PKE.ChallengeCCA [Interface.AdmissibleDistinguishers] [DecidableEq PK] [DecidableEq M]
    [DecidableEq C] (scheme : PublicKeyEncryption PK SK M C) {q : ℕ}
    (error : (PKEChallenge PK M C q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (PKE.ChallengeCCA.systems scheme q).1 ≃[error] (PKE.ChallengeCCA.systems scheme q).2

/-! ## Single-challenge CCA security of a KEM -/

-- The challenge of `IND-CCA^KEM(b)` [1, Figure 1] on the public key, `E_pk` and `D_sk`: at the
-- first query, `(c*, k₀) ← E(pk)` and `k₁ ← K`; the input is `(pk, c*, k_b)`; on `c`, output `⊥`
-- if `c = c*`, otherwise `D(sk, c)`.
converter KEM.ChallengeCCA.Challenge(PK C K : Type) [Fintype PK] [Fintype C] [Fintype K] [DecidableEq C] [Nonempty K] (b : Bool) : KEMChallenge PK C K
  inside kem : Encapsulation PK C K
  initialize
    challenge ← (none : Option (PK × C × K))
  on input() → PK × C × K
    match challenge
    | some x →
      return x
    | none →
      pk ← kem.publicKey()
      encapsulation ← kem.encaps()
      k₁ ←$ 𝒰[K]
      challenge ← some (pk, encapsulation.1, if b then k₁ else encapsulation.2)
      return (pk, encapsulation.1, if b then k₁ else encapsulation.2)
  on dec(c : C) → Option K
    match challenge
    | some x →
      if c = x.2.1
        return none
      else
        k ← kem.decaps(c)
        return k
    | none →
      pk ← kem.publicKey()
      encapsulation ← kem.encaps()
      k₁ ←$ 𝒰[K]
      challenge ← some (pk, encapsulation.1, if b then k₁ else encapsulation.2)
      if c = encapsulation.1
        return none
      else
        k ← kem.decaps(c)
        return k

/-- **The systems of single-challenge CCA security of a KEM** [1, Definition 2]: the challenge
for the bits `0` and `1` on the public key, `E_pk` and `D_sk` for `(pk, sk) ← Gen`, at a total
budget of `q` queries. -/
def KEM.ChallengeCCA.systems [Nonempty K] [DecidableEq PK] [DecidableEq C]
    (kem : KEM PK SK C K) (q : ℕ) :
    Interface.Resource (KEMChallenge PK C K q) × Interface.Resource (KEMChallenge PK C K q) :=
  (KEM.ChallengeCCA.Challenge PK C K false • KEM.Real kem,
    KEM.ChallengeCCA.Challenge PK C K true • KEM.Real kem)

/-- **Single-challenge CCA security of a KEM** within `error`: against the admitted
distinguishers, the challenge for the bit `0` substitutes for the challenge for the bit `1`. -/
def KEM.ChallengeCCA [Interface.AdmissibleDistinguishers] [Nonempty K] [DecidableEq PK]
    [DecidableEq C] (kem : KEM PK SK C K) {q : ℕ}
    (error : (KEMChallenge PK C K q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (KEM.ChallengeCCA.systems kem q).1 ≃[error] (KEM.ChallengeCCA.systems kem q).2

/-- **The correctness error** of a KEM is at most `δ`: for `(pk, sk) ← G` and `(c, k) ← E(pk)`,
the probability that `D(sk, c) ≠ k` is at most `δ`. -/
def KEM.CorrectnessError [DecidableEq PK] [DecidableEq SK] (kem : KEM PK SK C K) (δ : ℝ) : Prop :=
  (Distribution.ProbDist.bind kem.gen fun keys =>
      Distribution.ProbDist.map (fun ck => (keys, ck)) (kem.encaps keys.1)).1.mass
    (fun x => kem.decaps x.1.2 x.2.1 ≠ some x.2.2) ≤ δ

end

end Commons
