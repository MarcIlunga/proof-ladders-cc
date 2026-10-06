import Commons.Definitions.Signature
import ProofLadders.Common.Game
import ProofLadders.Common.Probability
import Mathlib.Data.ZMod.Basic

/-!
# Unilateral authenticated key exchange

The definitions of [1] for the key-exchange problems of the protocol ladder. As in [1], key
indistinguishability is a pair of systems, `IND⁰` and `IND¹`, whose advantage is a solver's
difference of decision probabilities, and SUF-CMA and strong CDH are winning games, whose
advantage is a solver's winning probability (`Interface.Game.ofWins`). Each notion is stated on
the real system of the scheme or of the assumption: key indistinguishability as a converter
applied to it, the games as a winning condition on its transcripts. Interface alphabets are
finite, so users and sessions are indexed by `Fin qgen` and `Fin qinit`, and a generation or
initiation past these bounds is refused.

* **Two-pass key exchange** [1, §2]: `KE = (gen, init, resp, recv)`, with a session key that may
  be `⊥`. The algorithms take the random oracle as an argument, which the real system samples
  once.
  Correctness, the game `CORR` of [1, Figure 5], is read session by session: for every oracle,
  an honestly forwarded session gives the responder a key `k ≠ ⊥` and the initiator the same
  key.
* **The real system** of a two-pass key exchange: its algorithms under stored responder keys and
  initiator states, with the oracles `Gen`, `Init`, `Receive`, `Respond`, `Corrupt` and `Expose`,
  beside the random oracle `H`, sampled once.
* **Key indistinguishability** [1, Figure 6]: `IND^b` is the converter `KeyExchange.IND b`,
  stated for every two-pass key exchange, applied to the real system. The converter keeps the
  game's sets and arrays, `P[·]`, `I[·]`, `Q`, `ICH`, `XP`, `CR` and `R[·]`, and replaces a
  challenged key by a uniform key when `b = 1`. The definition is the stronger one used in
  [1, §3], without line 17. A response is partnered with every initiator that processed the same
  transcript and intends its responder [1, §2]: `Respond` records it for all of them, and
  challenges only if none of them is exposed. When several responders have the intended public
  key, the first is taken (Remark 2 of [1]).
* **SUF-CMA and multi-user SUF-CMA** [1, Figures 3 and 4], as games on the real system of the
  scheme, `SignatureScheme.Real` and, for `users` users with corruption,
  `SignatureScheme.MultiReal`: the flag `win`, read off the transcript, is a verified triple of
  an uncorrupted user that `Sign` did not output. The final forgery of [1] is a verification
  query.
* **Strong CDH and multi-user strong CDH** [1, Figures 1 and 2], as games on the real systems of
  the assumption, `StCDH.Single` and `StCDH.Real`, with the challenges, corruption and the `DDH`
  oracle: the flag `win` is the solution, output as a query in the single-user game and found by
  a `DDH` query in the multi-user game. In the multi-user game the flag is read off the
  transcript: a `DDH(X, Y, Z)` query answered `1` on an `X` and a `Y` generated at uncorrupted
  indices, which is [1, Figure 2, lines 11–13], since with `X` and `Y` generated the reply `1`
  means `Z = Y^{x_i}`.
* **Key entropy** of a signature scheme [1, §1.3]: no public key has probability above
  `2^{-γ}`.

`Require x` of [1] ends the oracle without output, which is the reply `none`; a reply `⊥` of
the protocol is `none` inside it.

Upstream candidates: `SignatureScheme.KeyEntropy`, `MultiSigning`, `SignatureScheme.MultiReal`,
the flags `SignatureScheme.Forges` and `SignatureScheme.MultiForges` and the games
`SignatureScheme.SUFCMA.game` and `SignatureScheme.MultiSUFCMA.game` for
`Commons.Definitions.Signature`; `MultiStCDH`, `SingleStCDH`, `StCDH.Real`, `StCDH.Single`, the
flags `StCDH.Solved` and `StCDH.MultiSolved` and the games `StCDH.Single.game` and
`StCDH.Multi.game` for `Commons.Definitions.DiffieHellman`; `KeyExchange`,
`KeyExchange.Correct`, `UAKE`, `TwoPass`, `KeyExchange.Real`, `KeyExchange.IND` and
`KeyExchange.IND.systems` for a new module `Commons.Definitions.KeyExchange`.

## Main definitions

* `KeyExchange HIn HOut PK SK ST C₁ C₂ K`: two-pass key exchange in the random-oracle model
* `KeyExchange.Correct`: correctness
* `TwoPass`, `KeyExchange.Real ke`: the real system of a key exchange
* `UAKE`, `KeyExchange.IND b`, `KeyExchange.IND.systems`: key indistinguishability
* `SignatureScheme.SUFCMA.game`, `MultiSigning`, `SignatureScheme.MultiSUFCMA.game`: SUF-CMA
  and multi-user SUF-CMA
* `SingleStCDH`, `StCDH.Single.game`, `MultiStCDH`, `StCDH.Multi.game`: strong CDH and
  multi-user strong CDH
* `SignatureScheme.KeyEntropy`: key entropy

## References

1. D. Riepel and P. Rösler. *Basic definitions, constructions, and proofs for unilateral
   authenticated key exchange*. The protocol ladder, `proof-ladders/protocol-ladder`,
   `Notes/computational/main.pdf`, 2025.
-/

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

/-! ## Signatures -/

/-- **Key entropy** [1, §1.3]: key generation has `γ` bits of entropy when no public key has
probability above `2^{-γ}`. -/
def SignatureScheme.KeyEntropy {PK SK M Sig : Type} (scheme : SignatureScheme PK SK M Sig)
    (γ : ℕ) : Prop :=
  ∀ pk, scheme.gen.1.mass (fun keys => keys.1 = pk) ≤ 1 / 2 ^ γ

interface MultiSigning(PK SK M Sig : Type) [Fintype PK] [Fintype SK] [Fintype M] [Fintype Sig] (users : ℕ)
  gen() → Option PK
  sign(j : Fin users, m : M) → Option Sig
  corrupt(j : Fin users) → Option SK
  verify(j : Fin users, m : M, σ : Sig) → Bool

noncomputable section

variable {PK SK M Sig : Type} [Fintype PK] [Fintype SK] [Fintype M] [Fintype Sig]

-- `q-SUF-CMA` [1, Figure 4]: `Gen` generates the key pair of the next user, up to `users`;
-- `Sign(j, m)` and `Corrupt(j)` require `j ∈ [n]`; `verify(j, m, σ)` is `SIG.vfy(pk_j, m, σ)`.
system SignatureScheme.MultiReal(scheme : SignatureScheme PK SK M Sig) (users : ℕ) [DecidableEq SK] [DecidableEq M] : MultiSigning PK SK M Sig users
  initialize
    keys ← ([] : List (PK × SK))
  on gen() → Option PK
    if keys.length < users
      key ←$ scheme.gen
      keys ← keys ++ [key]
      return some key.1
    else
      return none
  on sign(j : Fin users, m : M) → Option Sig
    match keys[j.val]?
    | none →
      return none
    | some key →
      signatures ←$ scheme.signatures
      return some (signatures (key.2, m))
  on corrupt(j : Fin users) → Option SK
    return (keys[j.val]?).map Prod.snd
  on verify(j : Fin users, m : M, σ : Sig) → Bool
    match keys[j.val]?
    | none →
      return false
    | some key →
      return scheme.verify key.1 m σ

variable [DecidableEq M] [DecidableEq Sig]

section Single

variable {q : Signing.Port → ℕ}

/-- The set `Q` of a transcript: the messages with the signatures `Sign` returned. -/
def SignatureScheme.signed (h : (Signing.perPort PK M Sig q).Transcript) : List (M × Sig) :=
  h.filterMap fun
    | (⟨.sign, m⟩, ⟨.sign, σ⟩) => some (m, σ)
    | _ => none

/-- **The flag of SUF-CMA** [1, Figure 3, lines 03–04]: the last query verifies a pair that
`Sign` did not output. -/
def SignatureScheme.Forges (h : (Signing.perPort PK M Sig q).Transcript) : Prop :=
  ∃ m σ, h.getLast? = some (⟨.verify, (m, σ)⟩, ⟨.verify, true⟩) ∧
    (m, σ) ∉ SignatureScheme.signed h.dropLast

/-- **The SUF-CMA game** [1, Figure 3], at the budget `q` per port. -/
def SignatureScheme.SUFCMA.game [DecidableEq SK] (scheme : SignatureScheme PK SK M Sig)
    (q : Signing.Port → ℕ) : Interface.Game (Signing.perPort PK M Sig q) :=
  Interface.Game.ofWins (SignatureScheme.Real.perPort scheme) SignatureScheme.Forges

end Single

variable {users : ℕ} {q : MultiSigning.Port → ℕ}

/-- The set `Q` of a transcript: the triples of a user, a message and the signature `Sign`
returned. -/
def SignatureScheme.multiSigned (h : (MultiSigning.perPort PK SK M Sig users q).Transcript) :
    List (Fin users × M × Sig) :=
  h.filterMap fun
    | (⟨.sign, (j, m)⟩, ⟨.sign, some σ⟩) => some (j, m, σ)
    | _ => none

/-- The set `CR` of a transcript: the users whose key `Corrupt` returned. -/
def SignatureScheme.corrupted (h : (MultiSigning.perPort PK SK M Sig users q).Transcript) :
    List (Fin users) :=
  h.filterMap fun
    | (⟨.corrupt, j⟩, ⟨.corrupt, some _⟩) => some j
    | _ => none

/-- **The flag of `q`-SUF-CMA** [1, Figure 4, lines 03–04]: the last query verifies a triple of an
uncorrupted user that `Sign` did not output. -/
def SignatureScheme.MultiForges (h : (MultiSigning.perPort PK SK M Sig users q).Transcript) :
    Prop :=
  ∃ j m σ, h.getLast? = some (⟨.verify, (j, m, σ)⟩, ⟨.verify, true⟩) ∧
    j ∉ SignatureScheme.corrupted h.dropLast ∧ (j, m, σ) ∉ SignatureScheme.multiSigned h.dropLast

/-- **The `q`-SUF-CMA game** [1, Figure 4], for `users` users, at the budget `q` per port. -/
def SignatureScheme.MultiSUFCMA.game [DecidableEq SK] (scheme : SignatureScheme PK SK M Sig)
    (users : ℕ) (q : MultiSigning.Port → ℕ) :
    Interface.Game (MultiSigning.perPort PK SK M Sig users q) :=
  Interface.Game.ofWins (SignatureScheme.MultiReal.perPort scheme users)
    SignatureScheme.MultiForges

end

/-! ## Strong CDH -/

interface MultiStCDH(G : Type) [Fintype G] (p : ℕ) [NeZero p] (q₁ q₂ : ℕ)
  gen₁() → Option G
  gen₂() → Option G
  corrupt₁(i : Fin q₁) → Option (ZMod p)
  corrupt₂(j : Fin q₂) → Option (ZMod p)
  ddh(X : G, Y : G, Z : G) → Bool

interface SingleStCDH(G : Type) [Fintype G]
  challenge() → G × G
  ddh(X : G, Y : G, Z : G) → Bool
  solve(Z : G) → Bool

section StCDH

variable {G : Type} [Group G] [Fintype G] [DecidableEq G] {p : ℕ} [NeZero p]

/-- The `DDH` oracle of [1, Figure 2], lines 11–17: `1` if `X = g^{x_i}` and `Z = Y^{x_i}` for
some `i`, otherwise `[Z = X^{y_j}]` if `Y = g^{y_j}` for some `j`, and `0` otherwise. -/
def StCDH.ddh (g : G) (xs ys : List (ZMod p)) (X Y Z : G) : Bool :=
  if xs.any fun x => decide (X = g ^ x.val ∧ Z = Y ^ x.val) then true
  else match ys.find? fun y => decide (Y = g ^ y.val) with
    | some y => decide (Z = X ^ y.val)
    | none => false

noncomputable section

-- `(q₁, q₂)-St-CDH` [1, Figure 2]: `Gen₁` and `Gen₂` sample the next exponent, up to `q₁` and
-- `q₂`; `Corrupt₁(i)` and `Corrupt₂(j)` require an index already generated and return its
-- exponent; `DDH` is `StCDH.ddh`.
system StCDH.Real(p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) : MultiStCDH G p q₁ q₂
  initialize
    xs ← ([] : List (ZMod p))
    ys ← ([] : List (ZMod p))
  on gen₁() → Option G
    if xs.length < q₁
      x ←$ 𝒰[ZMod p]
      xs ← xs ++ [x]
      return some (g ^ x.val)
    else
      return none
  on gen₂() → Option G
    if ys.length < q₂
      y ←$ 𝒰[ZMod p]
      ys ← ys ++ [y]
      return some (g ^ y.val)
    else
      return none
  on corrupt₁(i : Fin q₁) → Option (ZMod p)
    return xs[i.val]?
  on corrupt₂(j : Fin q₂) → Option (ZMod p)
    return ys[j.val]?
  on ddh(X : G, Y : G, Z : G) → Bool
    return StCDH.ddh g xs ys X Y Z

-- `St-CDH` [1, Figure 1]: `x, y ← ℤ_p`; the challenge `(g^x, g^y)`; `DDH(X, Y, Z)` is
-- `[Z = Y^x]` if `X = g^x`, otherwise `[Z = X^y]` if `Y = g^y`, and `0` otherwise; the output
-- `Z` is answered `[Z = g^{xy}]`.
system StCDH.Single(p : ℕ) [NeZero p] (g : G) : SingleStCDH G
  initialize
    x ←$ 𝒰[ZMod p]
    y ←$ 𝒰[ZMod p]
  on challenge() → G × G
    return (g ^ x.val, g ^ y.val)
  on ddh(X : G, Y : G, Z : G) → Bool
    if X = g ^ x.val
      return decide (Z = Y ^ x.val)
    else
      if Y = g ^ y.val
        return decide (Z = X ^ y.val)
      else
        return false
  on solve(Z : G) → Bool
    return decide (Z = g ^ (x * y).val)

section Single

variable {q : SingleStCDH.Port → ℕ}

/-- **The flag of St-CDH** [1, Figure 1, line 02]: the output is the solution. -/
def StCDH.Solved (h : (SingleStCDH.perPort G q).Transcript) : Prop :=
  ∃ Z, h.getLast? = some (⟨.solve, Z⟩, ⟨.solve, true⟩)

/-- **The St-CDH game** [1, Figure 1], at the budget `q` per port. -/
def StCDH.Single.game (p : ℕ) [NeZero p] (g : G) (q : SingleStCDH.Port → ℕ) :
    Interface.Game (SingleStCDH.perPort G q) :=
  Interface.Game.ofWins (StCDH.Single.perPort p g) StCDH.Solved

end Single

variable {q₁ q₂ : ℕ} {q : MultiStCDH.Port → ℕ}

/-- The challenges `g^{x_i}` of a transcript: the replies of `Gen₁`, in order. -/
def MultiStCDH.challenges₁ (h : (MultiStCDH.perPort G p q₁ q₂ q).Transcript) : List G :=
  h.filterMap fun
    | (⟨.gen₁, _⟩, ⟨.gen₁, some X⟩) => some X
    | _ => none

/-- The challenges `g^{y_j}` of a transcript: the replies of `Gen₂`, in order. -/
def MultiStCDH.challenges₂ (h : (MultiStCDH.perPort G p q₁ q₂ q).Transcript) : List G :=
  h.filterMap fun
    | (⟨.gen₂, _⟩, ⟨.gen₂, some Y⟩) => some Y
    | _ => none

/-- The set `CR₁` of a transcript: the indices whose exponent `Corrupt₁` returned. -/
def MultiStCDH.corrupted₁ (h : (MultiStCDH.perPort G p q₁ q₂ q).Transcript) : List (Fin q₁) :=
  h.filterMap fun
    | (⟨.corrupt₁, i⟩, ⟨.corrupt₁, some _⟩) => some i
    | _ => none

/-- The set `CR₂` of a transcript: the indices whose exponent `Corrupt₂` returned. -/
def MultiStCDH.corrupted₂ (h : (MultiStCDH.perPort G p q₁ q₂ q).Transcript) : List (Fin q₂) :=
  h.filterMap fun
    | (⟨.corrupt₂, j⟩, ⟨.corrupt₂, some _⟩) => some j
    | _ => none

/-- **The flag of `(q₁, q₂)`-St-CDH** [1, Figure 2, lines 11–13]: the last query is `DDH(X, Y, Z)`,
answered `1`, on an `X` and a `Y` generated at uncorrupted indices. -/
def StCDH.MultiSolved (h : (MultiStCDH.perPort G p q₁ q₂ q).Transcript) : Prop :=
  ∃ X Y Z, h.getLast? = some (⟨.ddh, (X, Y, Z)⟩, ⟨.ddh, true⟩) ∧
    ∃ (i : Fin q₁) (j : Fin q₂), (MultiStCDH.challenges₁ h.dropLast)[i.val]? = some X ∧
      (MultiStCDH.challenges₂ h.dropLast)[j.val]? = some Y ∧
      i ∉ MultiStCDH.corrupted₁ h.dropLast ∧ j ∉ MultiStCDH.corrupted₂ h.dropLast

/-- **The `(q₁, q₂)`-St-CDH game** [1, Figure 2], at the budget `q` per port. -/
def StCDH.Multi.game (p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) (q : MultiStCDH.Port → ℕ) :
    Interface.Game (MultiStCDH.perPort G p q₁ q₂ q) :=
  Interface.Game.ofWins (StCDH.Real.perPort p g q₁ q₂) StCDH.MultiSolved

end

end StCDH

/-! ## Two-pass key exchange -/

/-- **A two-pass key exchange** [1, §2] in the random-oracle model, the oracle being an argument
of the algorithms: long-term key generation for responders, the initiator's first step, the
responder's step, and the initiator's final step. A session key `⊥` is `none`. -/
structure KeyExchange (HIn HOut PK SK ST C₁ C₂ K : Type) where
  /-- `KE.gen`: a responder key pair. -/
  gen : Distribution.ProbDist (SK × PK)
  /-- `KE.init(pk)`: the initiator's state and first message. -/
  init : (HIn → HOut) → PK → Distribution.ProbDist (ST × C₁)
  /-- `KE.resp(sk, c)`: the responder's key and reply. -/
  resp : (HIn → HOut) → SK → C₁ → Distribution.ProbDist (Option K × C₂)
  /-- `KE.recv(st, c')`: the initiator's key. -/
  recv : (HIn → HOut) → ST → C₂ → Option K

/-- **Correctness** [1, Figure 5], session by session: for every oracle, generated key pair, run of
`init`, and run of `resp` on its message, the responder's key is not `⊥` and `recv` gives the
initiator the same key. -/
def KeyExchange.Correct {HIn HOut PK SK ST C₁ C₂ K : Type}
    (ke : KeyExchange HIn HOut PK SK ST C₁ C₂ K) : Prop :=
  ∀ H, ∀ keys ∈ ke.gen.1.support, ∀ start ∈ (ke.init H keys.2).1.support,
    ∀ response ∈ (ke.resp H keys.1 start.2).1.support,
      response.1.isSome ∧ ke.recv H start.1 response.2 = response.1

interface UAKE(HIn HOut PK SK ST C₁ C₂ K : Type) [Fintype HIn] [Fintype HOut] [Fintype PK] [Fintype SK] [Fintype ST] [Fintype C₁] [Fintype C₂] [Fintype K] (qgen qinit : ℕ)
  gen() → Option PK
  init(pk : PK) → Option C₁
  receive(i : Fin qinit, c : C₂, ch : Bool) → Option (Option K)
  respond(j : Fin qgen, c : C₁, ch : Bool) → Option (Option K × C₂)
  corrupt(j : Fin qgen) → Option SK
  expose(i : Fin qinit) → Option ST
  hash(x : HIn) → HOut

interface TwoPass(HIn HOut PK SK ST C₁ C₂ K : Type) [Fintype HIn] [Fintype HOut] [Fintype PK] [Fintype SK] [Fintype ST] [Fintype C₁] [Fintype C₂] [Fintype K] (qgen qinit : ℕ)
  gen() → Option PK
  init(pk : PK) → Option C₁
  receive(i : Fin qinit, c : C₂) → Option (Option K)
  respond(j : Fin qgen, c : C₁) → Option (Option K × C₂)
  corrupt(j : Fin qgen) → Option SK
  expose(i : Fin qinit) → Option ST
  hash(x : HIn) → HOut

noncomputable section

variable {HIn HOut PK SK ST C₁ C₂ K : Type} [Fintype HIn] [Fintype HOut] [Fintype PK]
  [Fintype SK] [Fintype ST] [Fintype C₁] [Fintype C₂] [Fintype K]

/-- Independent runs of `KE.init` for every oracle and public key. -/
def KeyExchange.inits [DecidableEq HIn] [DecidableEq HOut] [DecidableEq PK]
    (ke : KeyExchange HIn HOut PK SK ST C₁ C₂ K) :
    Distribution.ProbDist ((HIn → HOut) × PK → ST × C₁) :=
  Distribution.ProbDist.pi fun x => ke.init x.1 x.2

/-- Independent runs of `KE.resp` for every oracle, secret key and first message. -/
def KeyExchange.resps [DecidableEq HIn] [DecidableEq HOut] [DecidableEq SK] [DecidableEq C₁]
    (ke : KeyExchange HIn HOut PK SK ST C₁ C₂ K) :
    Distribution.ProbDist ((HIn → HOut) × SK × C₁ → Option K × C₂) :=
  Distribution.ProbDist.pi fun x => ke.resp x.1 x.2.1 x.2.2

-- The real system of `KE` [1, Figure 6], with the random oracle `H` sampled once: `Gen` stores
-- `(sk_m, pk_m) ←$ KE.gen`, up to `qgen`; `Init(pk)` stores `st_n` of `(st_n, c) ←$ KE.init(pk)`,
-- up to `qinit`; `Receive(i, c)` is `KE.recv(st_i, c)` and `Respond(j, c)` is `KE.resp(sk_j, c)`,
-- requiring `i ∈ [n]` and `j ∈ [m]`; `Corrupt(j)` and `Expose(i)` return `sk_j` and `st_i`.
system KeyExchange.Real(ke : KeyExchange HIn HOut PK SK ST C₁ C₂ K) (qgen qinit : ℕ) [Nonempty HOut] [DecidableEq HIn] [DecidableEq HOut] [DecidableEq PK] [DecidableEq SK] [DecidableEq C₁] : TwoPass HIn HOut PK SK ST C₁ C₂ K qgen qinit
  initialize
    H ←$ 𝒰[HIn → HOut]
    keys ← ([] : List (SK × PK))
    states ← ([] : List ST)
  on gen() → Option PK
    if keys.length < qgen
      key ←$ ke.gen
      keys ← keys ++ [key]
      return some key.2
    else
      return none
  on init(pk : PK) → Option C₁
    if states.length < qinit
      inits ←$ ke.inits
      states ← states ++ [(inits (H, pk)).1]
      return some (inits (H, pk)).2
    else
      return none
  on receive(i : Fin qinit, c : C₂) → Option (Option K)
    return (states[i.val]?).map fun st => ke.recv H st c
  on respond(j : Fin qgen, c : C₁) → Option (Option K × C₂)
    match keys[j.val]?
    | none →
      return none
    | some key →
      resps ←$ ke.resps
      return some (resps (H, key.1, c))
  on corrupt(j : Fin qgen) → Option SK
    return (keys[j.val]?).map Prod.fst
  on expose(i : Fin qinit) → Option ST
    return states[i.val]?
  on hash(x : HIn) → HOut
    return H x

-- `IND^b` [1, Figure 6], without line 17, on the real system of a two-pass key exchange: `Gen`
-- records `pk_m`; `Init(pk)` records `I[n] = c` and `P[n]`, the first `j` with `pk = pk_j`;
-- `Receive(i, c, ch)` requires `i ∈ [n] \ Q`, returns nothing on `c ∈ R[P[i], i]`, and
-- challenges when `i ∉ XP`, `P[i] ∈ [m] \ CR` and `k ≠ ⊥`; `Respond(j, c, ch)` records `c′` in
-- `R[j, i]` for every partnered `i`, those with `P[i] = j ∧ I[i] = c`, and challenges when none
-- of them is in `XP`, adding all of them to `ICH`; a challenge replaces `k` by `k ←$ K` when
-- `b = 1`; `Corrupt(j)` adds `j` to `CR`; `Expose(i)` requires `i ∉ ICH` and adds `i` to `XP`.
converter KeyExchange.IND(HIn HOut PK SK ST C₁ C₂ K : Type) [Fintype HIn] [Fintype HOut] [Fintype PK] [Fintype SK] [Fintype ST] [Fintype C₁] [Fintype C₂] [Fintype K] (b : Bool) (qgen qinit : ℕ) [Nonempty K] [DecidableEq PK] [DecidableEq C₁] [DecidableEq C₂] : UAKE HIn HOut PK SK ST C₁ C₂ K qgen qinit
  inside ke : TwoPass HIn HOut PK SK ST C₁ C₂ K qgen qinit
  initialize
    pks ← ([] : List PK)
    P ← ([] : List (Option (Fin qgen)))
    I ← ([] : List C₁)
    Q ← ([] : List (Fin qinit))
    ICH ← ([] : List (Fin qinit))
    XP ← ([] : List (Fin qinit))
    CR ← ([] : List (Fin qgen))
    R ← ([] : List (Fin qgen × Fin qinit × C₂))
  on gen() → Option PK
    pk ← ke.gen()
    pks ← pks ++ pk.toList
    return pk
  on init(pk : PK) → Option C₁
    reply ← ke.init(pk)
    match reply
    | none →
      return none
    | some c →
      P ← P ++ [(List.finRange qgen).find? fun j => decide (pks[j.val]? = some pk)]
      I ← I ++ [c]
      return some c
  on receive(i : Fin qinit, c : C₂, ch : Bool) → Option (Option K)
    match P[i.val]?
    | none →
      return none
    | some partner →
      if decide (i ∈ Q)
        return none
      else
        Q ← Q ++ [i]
        if decide (∃ j, partner = some j ∧ (j, i, c) ∈ R)
          return none
        else
          reply ← ke.receive(i, c)
          match reply
          | none →
            return none
          | some k →
            if (ch && !decide (i ∈ XP) && decide (∃ j, partner = some j ∧ j ∉ CR) && k.isSome)
              ICH ← ICH ++ [i]
              if b
                key ←$ 𝒰[K]
                return some (some key)
              else
                return some k
            else
              return some k
  on respond(j : Fin qgen, c : C₁, ch : Bool) → Option (Option K × C₂)
    reply ← ke.respond(j, c)
    match reply
    | none →
      return none
    | some (k, c') →
      partners ← (List.finRange qinit).filter (fun i =>
        decide (P[i.val]? = some (some j) ∧ I[i.val]? = some c))
      if decide (partners = [])
        return some (k, c')
      else
        R ← R ++ partners.map fun i => (j, i, c')
        if ch && decide (∀ i ∈ partners, i ∉ XP)
          ICH ← ICH ++ partners
          if b
            key ←$ 𝒰[K]
            return some (some key, c')
          else
            return some (k, c')
        else
          return some (k, c')
  on corrupt(j : Fin qgen) → Option SK
    sk ← ke.corrupt(j)
    CR ← CR ++ sk.toList.map fun _ => j
    return sk
  on expose(i : Fin qinit) → Option ST
    if decide (i ∈ ICH)
      return none
    else
      st ← ke.expose(i)
      XP ← XP ++ st.toList.map fun _ => i
      return st
  on hash(x : HIn) → HOut
    h ← ke.hash(x)
    return h

/-- **The systems of key indistinguishability** [1, Figure 6]: `IND⁰` and `IND¹`, the converter
`KeyExchange.IND b` on the real system of `KE`, for `qgen` responders and `qinit` initiator
sessions, at the budget `q` per port. -/
def KeyExchange.IND.systems [Nonempty HOut] [Nonempty K] [DecidableEq HIn] [DecidableEq HOut]
    [DecidableEq PK] [DecidableEq SK] [DecidableEq C₁] [DecidableEq C₂]
    (ke : KeyExchange HIn HOut PK SK ST C₁ C₂ K) (qgen qinit : ℕ) (q : UAKE.Port → ℕ) :
    Interface.Resource (UAKE.perPort HIn HOut PK SK ST C₁ C₂ K qgen qinit q) ×
      Interface.Resource (UAKE.perPort HIn HOut PK SK ST C₁ C₂ K qgen qinit q) :=
  (KeyExchange.IND.perPort HIn HOut PK SK ST C₁ C₂ K false qgen qinit •
      KeyExchange.Real.perPort ke qgen qinit,
    KeyExchange.IND.perPort HIn HOut PK SK ST C₁ C₂ K true qgen qinit •
      KeyExchange.Real.perPort ke qgen qinit)

end

end Commons
