import ProofLadders.Common.Symmetric
import ProofLadders.Common.Programs

/-!
# Basic Hash

Problem 1 of the protocol ladder [1, §2.1]: a tag `T` with key `t_sk` sends a fresh nonce `n` and
`H(n, t_sk)`; the reader accepts if the hash matches one of its keys. In the computational model
of [2], `H(n, t_sk) = F(t_sk, n)` for a keyed function `F`, there are `nTag` tags, each running
at most `nSession` sessions, and one reader. A tag past its sessions answers `⊥`.

* **Authentication** (unilateral, non-injective): if the reader accepts a message, a tag sent it.
  As a substitution, the protocol is indistinguishable from the one whose reader accepts only
  messages that a tag sent (`Auth`). The assumption is the unforgeable PRF of [2] under the
  `nTag` tag keys; its two applications are the swap to the random function, whose reader already
  accepts only sent messages, and the swap back under `Auth`.
* **Unlinkability**: the protocol in which each tag keeps its key for all its sessions
  (`Multiple`) is indistinguishable from the one in which every session has its own key
  (`Single`). As in [2], the loss is the unforgeable-PRF loss under `nTag` keys and under
  `nTag · nSession` keys, and the probability `nSession² · nTag / |N|` that a tag repeats a
  nonce, the only difference between the two protocols under random functions.
* **The bonus** of [1, §2.1]: injective authentication fails by a replay. Replaying an accepted
  message distinguishes the protocol from the one that accepts each sent message once.

The reductions are the protocols on the oracles of the unforgeable PRF, the modules `Multiple0`
and `Single0` of [2]: a tag query is one evaluation, under the tag's key or the key of its
session, and a reader query checks the message under every key, in a loop. The distinguisher of
[2] is the adversary with a reduction absorbed; for authentication the second application is
under `Auth ≫ Multiple0`, whose log of sent messages is that of [2]. The reductions are typed at
per-label inside budgets (`Interface.Converter.ofLabelBoundedProgram`), a reader query making
`nTag`, or `nTag · nSession`, checks.

Style: pure random systems; the nonce collision is a bad event of systems that sample a nonce per
query, not of sampled functions, so it is counted in the loss.

Upstream candidates: `Program.LabelCallBound.mono`, `Program.labelCallBound_call_single` and
`Program.labelCallBound_foldr`, the per-label bounds of loops, for
`RandomSystems.Converter.Program` beside `Program.labelCallBound_call` of `Common/Programs`.

## Main definitions

* `TagReader N T nTag`: the interface of the tags and the reader
* `Multiple F nTag nSession`, `Single F nTag nSession`: the protocol with one key per tag, and
  with one key per session
* `Auth`, `InjectiveAuth`: the readers that accept only sent messages, and each at most once
* `Multiple0`, `Single0`: the reductions of [2], and their typings `.perLabel` at per-label
  inside budgets `multipleBudget`, `singleBudget`

## Main results

* `basic_hash_authentication`, `basic_hash_unlinkability`, `basic_hash_replay`

## References

1. The protocol ladder, `proof-ladders/protocol-ladder`, `Notes/main.tex`.
2. The protocol ladder, Basic Hash in EasyCrypt, `basic-hash/EasyCrypt/basic-hash-auth.ec` and
   `basic-hash-unlink.ec`.
-/

/-! ## Per-label bounds of loops (upstream candidate) -/

namespace SystemAlgebra.Program

variable {J : Type} {X Y : J → Type}

/-- A per-label call bound holds at every larger bound. -/
lemma LabelCallBound.mono {A : Type} {n n' : J → ℕ}
    {f : List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)} (hf : LabelCallBound n f)
    (hn : ∀ j, n j ≤ n' j) : LabelCallBound n' f :=
  fun h q hc hq => (hf h q hc hq).trans_le (hn q.1)

/-- A call at `j` adds one query at `j` to the bound of its continuation. -/
lemma labelCallBound_call_single {A : Type} [DecidableEq J] {n : J → ℕ} (j : J) (x : X j)
    (k : Y j → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j))
    (hk : ∀ y, LabelCallBound n (k y)) :
    LabelCallBound (n + Pi.single j 1) (DSL.callProg j x k) := by
  refine labelCallBound_call j x k (by simp) fun y => ?_
  convert hk y using 1
  funext i
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-- **A loop** makes the queries of its final continuation and at most `b j` queries at `j` per
element. -/
lemma labelCallBound_foldr {T C A : Type} (xs : List T)
    (step : T → (C → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)) →
      C → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j))
    (finish : C → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j))
    (a b : J → ℕ) (ha : ∀ c, LabelCallBound a (finish c))
    (hb : ∀ x n k, (∀ c, LabelCallBound n (k c)) → ∀ c, LabelCallBound (n + b) (step x k c))
    (c : C) : LabelCallBound (a + xs.length • b) (xs.foldr step finish c) := by
  induction xs generalizing c with
  | nil => simpa using ha c
  | cons x xs ih =>
    simpa only [List.foldr_cons, List.length_cons, succ_nsmul, add_assoc] using
      hb x (a + xs.length • b) (xs.foldr step finish) ih c

end SystemAlgebra.Program

namespace ProofLadders.BasicHash

open CategoryTheory Commons Probability SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface
open scoped SystemAlgebra SystemAlgebra.DSL

interface TagReader(N T : Type) [Fintype N] [Fintype T] (nTag : ℕ)
  tag(i : Fin nTag) → Option (N × T)
  reader(n : N, h : T) → Bool

noncomputable section

section Systems

variable {K N T : Type} [Fintype K] [Fintype N] [Fintype T]

-- `Multiple` [2]: tag `i` has the key `k_i` for all its sessions; a session samples `n` and
-- sends `(n, F(k_i, n))`; the reader accepts `(n, h)` if `F(k_i, n) = h` for some tag `i`.
system Multiple(F : K → N → T) (nTag nSession : ℕ) [Nonempty K] [Nonempty N] [DecidableEq T] : TagReader N T nTag
  initialize
    keys ←$ 𝒰[Fin nTag → K]
    sessions ← (fun _ => 0 : Fin nTag → ℕ)
  on tag(i : Fin nTag) → Option (N × T)
    if sessions i < nSession
      n ←$ 𝒰[N]
      sessions ← Function.update sessions i (sessions i + 1)
      return some (n, F (keys i) n)
    else
      return none
  on reader(n : N, h : T) → Bool
    return decide (∃ i, F (keys i) n = h)

-- `Single` [2]: session `s` of tag `i` has its own key `k_{i,s}`; the reader accepts `(n, h)`
-- if `F(k_{i,s}, n) = h` for some session.
system Single(F : K → N → T) (nTag nSession : ℕ) [Nonempty K] [Nonempty N] [DecidableEq T] : TagReader N T nTag
  initialize
    keys ←$ 𝒰[Fin nTag × Fin nSession → K]
    sessions ← (fun _ => 0 : Fin nTag → ℕ)
  on tag(i : Fin nTag) → Option (N × T)
    match (List.finRange nSession).find? fun s => s.val = sessions i
    | none →
      return none
    | some s →
      n ←$ 𝒰[N]
      sessions ← Function.update sessions i (sessions i + 1)
      return some (n, F (keys (i, s)) n)
  on reader(n : N, h : T) → Bool
    return decide (∃ i s, F (keys (i, s)) n = h)

-- Record the messages the tags send; accept only a sent message that the reader accepts.
converter Auth(N T : Type) [Fintype N] [Fintype T] [DecidableEq N] [DecidableEq T] (nTag : ℕ) : TagReader N T nTag
  inside protocol : TagReader N T nTag
  initialize
    sent ← ([] : List (N × T))
  on tag(i : Fin nTag) → Option (N × T)
    message ← protocol.tag(i)
    sent ← sent ++ message.toList
    return message
  on reader(n : N, h : T) → Bool
    valid ← protocol.reader(n, h)
    return valid && decide ((n, h) ∈ sent)

-- Record the messages the tags send; accept a sent message that the reader accepts, once.
converter InjectiveAuth(N T : Type) [Fintype N] [Fintype T] [DecidableEq N] [DecidableEq T] (nTag : ℕ) : TagReader N T nTag
  inside protocol : TagReader N T nTag
  initialize
    sent ← ([] : List (N × T))
    accepted ← ([] : List (N × T))
  on tag(i : Fin nTag) → Option (N × T)
    message ← protocol.tag(i)
    sent ← sent ++ message.toList
    return message
  on reader(n : N, h : T) → Bool
    valid ← protocol.reader(n, h)
    if valid && decide ((n, h) ∈ sent ∧ (n, h) ∉ accepted)
      accepted ← accepted ++ [(n, h)]
      return true
    else
      return false

end Systems

/-! ## The reductions -/

-- `Multiple0` [2]: the protocol on the oracles under the `nTag` tag keys; a session of tag `i`
-- samples `n` and sends `(n, f(i, n))`; the reader accepts `(n, h)` if `check(i, n, h)` for some
-- tag `i`. The session counters are bounded by `nSession`.
converter Multiple0(N T : Type) [Fintype N] [Fintype T] [Nonempty N] (nTag nSession : ℕ) : TagReader N T nTag
  inside prf : Checking (Fin nTag) N T
  initialize
    sessions ← (fun _ => 0 : Fin nTag → Fin (nSession + 1))
  on tag(i : Fin nTag) → Option (N × T)
    if sessions i < Fin.last nSession
      n ←$ 𝒰[N]
      h ← prf.f(i, n)
      sessions ← Function.update sessions i (sessions i + 1)
      return some (n, h)
    else
      return none
  on reader(n : N, h : T) → Bool
    b ← false
    for i ∈ List.finRange nTag
      r ← prf.check(i, n, h)
      b ← b || r
    return b

-- `Single0` [2]: the protocol on the oracles under the `nTag · nSession` session keys; session `s`
-- of tag `i` samples `n` and sends `(n, f((i, s), n))`; the reader accepts `(n, h)` if
-- `check((i, s), n, h)` for some session.
converter Single0(N T : Type) [Fintype N] [Fintype T] [Nonempty N] (nTag nSession : ℕ) : TagReader N T nTag
  inside prf : Checking (Fin nTag × Fin nSession) N T
  initialize
    sessions ← (fun _ => 0 : Fin nTag → Fin (nSession + 1))
  on tag(i : Fin nTag) → Option (N × T)
    match (List.finRange nSession).find? fun s => s.val = (sessions i).val
    | none →
      return none
    | some s →
      n ←$ 𝒰[N]
      h ← prf.f((i, s), n)
      sessions ← Function.update sessions i (sessions i + 1)
      return some (n, h)
  on reader(n : N, h : T) → Bool
    b ← false
    for i ∈ List.finRange nTag
      b₀ ← false
      for s ∈ List.finRange nSession
        r ← prf.check((i, s), n, h)
        b₀ ← b₀ || r
      b ← b || b₀
    return b

/-- The budget of the oracles under `Multiple0`: an evaluation per tag query, `nTag` checks per
reader query. -/
def multipleBudget (nTag : ℕ) (q : TagReader.Port → ℕ) : Checking.Port → ℕ
  | .f => q .tag
  | .check => nTag * q .reader

/-- The budget of the oracles under `Single0`: an evaluation per tag query, `nTag · nSession`
checks per reader query. -/
def singleBudget (nTag nSession : ℕ) (q : TagReader.Port → ℕ) : Checking.Port → ℕ
  | .f => q .tag
  | .check => nTag * nSession * q .reader

/-- The inside calls of `Multiple0` per procedure: an evaluation and a nonce per tag query, and
`nTag` checks per reader query. -/
def Multiple0.calls (nTag : ℕ) : TagReader.Port → Checking.Port ⊕ Unit → ℕ
  | .tag, .inl .f => 1
  | .reader, .inl .check => nTag
  | .tag, .inr _ => 1
  | _, _ => 0

/-- The inside calls of `Single0` per procedure: an evaluation and a nonce per tag query, and
`nTag · nSession` checks per reader query. -/
def Single0.calls (nTag nSession : ℕ) : TagReader.Port → Checking.Port ⊕ Unit → ℕ
  | .tag, .inl .f => 1
  | .reader, .inl .check => nTag * nSession
  | .tag, .inr _ => 1
  | _, _ => 0

variable {N T : Type} [Fintype N] [Fintype T] [Nonempty N]

/-- `Multiple0` calls each inside label at most `Multiple0.calls` times per procedure. -/
lemma Multiple0.labelBounded (nTag nSession : ℕ) :
    (Multiple0.body N T nTag nSession).LabelBounded (Multiple0.calls nTag) := by
  intro s o u
  cases o <;> simp only [Multiple0.body] <;> cases s <;> dsimp only
  any_goals
    repeat' (first
      | exact Program.labelCallBound_return _ _
      | (refine Program.labelCallBound_call _ _ _ (by simp [Multiple0.calls]) fun y => ?_)
      | split)
  all_goals
    refine (Program.labelCallBound_foldr _ _ _ 0
      (Pi.single (Sum.inl Checking.Port.check : Checking.Port ⊕ Unit) 1)
      (fun _ => Program.labelCallBound_return _ _)
      (fun _ _ _ hk _ => Program.labelCallBound_call_single _ _ _ fun _ => hk _) _).mono
      fun j => ?_
    rcases j with (_ | _) | _ <;> simp [Multiple0.calls]

/-- `Single0` calls each inside label at most `Single0.calls` times per procedure. -/
lemma Single0.labelBounded (nTag nSession : ℕ) :
    (Single0.body N T nTag nSession).LabelBounded (Single0.calls nTag nSession) := by
  intro s o u
  cases o <;> simp only [Single0.body] <;> cases s <;> dsimp only
  any_goals
    repeat' (first
      | exact Program.labelCallBound_return _ _
      | (refine Program.labelCallBound_call _ _ _ (by simp [Single0.calls]) fun y => ?_)
      | split)
  all_goals
    refine (Program.labelCallBound_foldr _ _ _ 0
      (nSession • Pi.single (Sum.inl Checking.Port.check : Checking.Port ⊕ Unit) 1)
      (fun _ => Program.labelCallBound_return _ _)
      (fun _ n _ hk _ => (Program.labelCallBound_foldr _ _ _ n (Pi.single _ 1) (fun _ => hk _)
        (fun _ _ _ hk' _ => Program.labelCallBound_call_single _ _ _ fun _ => hk' _) _).mono
          fun _ => by simp) _).mono
      fun j => ?_
    rcases j with (_ | _) | _ <;> simp [Single0.calls]

/-- The inside interface of the program of `Multiple0`: the oracles beside the source of
nonces. -/
abbrev Multiple0.inside (N T : Type) [Fintype N] [Fintype T] [Nonempty N] (nTag nSession : ℕ)
    (q : TagReader.Port → ℕ) : Interface :=
  (Checking.perPort (Fin nTag) N T (multipleBudget nTag q)).tensor
    (Interface.source (lawType (Multiple0.law1 N T nTag nSession)) (∑ i, q i))

/-- The inside interface of the program of `Single0`: the oracles beside the source of nonces. -/
abbrev Single0.inside (N T : Type) [Fintype N] [Fintype T] [Nonempty N] (nTag nSession : ℕ)
    (q : TagReader.Port → ℕ) : Interface :=
  (Checking.perPort (Fin nTag × Fin nSession) N T (singleBudget nTag nSession q)).tensor
    (Interface.source (lawType (Single0.law1 N T nTag nSession)) (∑ i, q i))

/-- The inside interface admits the per-label budget of `Multiple0`. -/
lemma Multiple0.admits (nTag nSession : ℕ) (q : TagReader.Port → ℕ) :
    (Multiple0.inside N T nTag nSession q).AdmitsLabelBudget
      fun j => ∑ o, Multiple0.calls nTag o j * q o := by
  refine ((portBudget_admitsLabelBudget _ _ _ _).tensor
    (queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simp))).mono fun j => ?_
  rcases j with (_ | _) | _ <;>
    simp [Finset.univ, Fintype.elems, Multiple0.calls, multipleBudget]

/-- The inside interface admits the per-label budget of `Single0`. -/
lemma Single0.admits (nTag nSession : ℕ) (q : TagReader.Port → ℕ) :
    (Single0.inside N T nTag nSession q).AdmitsLabelBudget
      fun j => ∑ o, Single0.calls nTag nSession o j * q o := by
  refine ((portBudget_admitsLabelBudget _ _ _ _).tensor
    (queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simp))).mono fun j => ?_
  rcases j with (_ | _) | _ <;>
    simp [Finset.univ, Fintype.elems, Single0.calls, singleBudget]

/-- **`Multiple0` at per-port budgets**: the program at the per-label call bound
`Multiple0.calls`, beside its source of nonces. -/
def Multiple0.perLabel (N T : Type) [Fintype N] [Fintype T] [Nonempty N] (nTag nSession : ℕ)
    (q : TagReader.Port → ℕ) :
    TagReader.perPort N T nTag q ⟶ Checking.perPort (Fin nTag) N T (multipleBudget nTag q) :=
  Converter.ofLabelBoundedProgram (A := TagReader.perPort N T nTag q)
      (B := Multiple0.inside N T nTag nSession q) none (Multiple0.body N T nTag nSession)
      (Multiple0.bound_spec N T nTag nSession) (Multiple0.calls nTag)
      (Multiple0.labelBounded nTag nSession) q (fun _ hd => hd.2)
      (Multiple0.admits nTag nSession q) ≫
    Interface.rightContext _ (Multiple0.randomness N T nTag nSession (∑ i, q i))

/-- **`Single0` at per-port budgets**: the program at the per-label call bound `Single0.calls`,
beside its source of nonces. -/
def Single0.perLabel (N T : Type) [Fintype N] [Fintype T] [Nonempty N] (nTag nSession : ℕ)
    (q : TagReader.Port → ℕ) :
    TagReader.perPort N T nTag q ⟶
      Checking.perPort (Fin nTag × Fin nSession) N T (singleBudget nTag nSession q) :=
  Converter.ofLabelBoundedProgram (A := TagReader.perPort N T nTag q)
      (B := Single0.inside N T nTag nSession q) none (Single0.body N T nTag nSession)
      (Single0.bound_spec N T nTag nSession) (Single0.calls nTag nSession)
      (Single0.labelBounded nTag nSession) q (fun _ hd => hd.2)
      (Single0.admits nTag nSession q) ≫
    Interface.rightContext _ (Single0.randomness N T nTag nSession (∑ i, q i))

end

/-! ## Authentication, unlinkability and the replay -/

noncomputable section

variable {K N T : Type} [Fintype K] [Fintype N] [Fintype T]
variable [Nonempty K] [Nonempty N] [Nonempty T] [DecidableEq N] [DecidableEq T]

/-- **Authentication** [1, §2.1]: if `F` is an unforgeable PRF under `nTag` keys within `ε`, the
protocol substitutes for the one whose reader accepts only sent messages, within the losses of
the two swaps, at `Multiple0` and at `Auth ≫ Multiple0`. -/
theorem basic_hash_authentication [AdmissibleDistinguishers] (F : K → N → T)
    (nTag nSession : ℕ) (q : TagReader.Port → ℕ) :
    ∀ ε, PRF.EUF F (Fin nTag) ε →
      Multiple.perPort F nTag nSession ≃[fun D =>
          ε (absorb (Multiple0.perLabel N T nTag nSession q) D) +
            ε (absorb (Auth.perPort N T nTag ≫ Multiple0.perLabel N T nTag nSession q) D)]
        Auth.perPort N T nTag • Multiple.perPort F nTag nSession := by
  -- `Multiple = Multiple0 • PRFs ≃ Multiple0 • EUF_RF = (Auth ≫ Multiple0) • EUF_RF ≃
  -- (Auth ≫ Multiple0) • PRFs = Auth • Multiple`, since the reader of `Multiple0 • EUF_RF`
  -- accepts only sent messages.
  sorry

/-- **Unlinkability** [1, §2.1], [2]: if `F` is an unforgeable PRF under `nTag` keys within
`εm` and under `nTag · nSession` keys within `εs`, then `Multiple` substitutes for `Single`
within the two losses, at `Multiple0` and `Single0`, and `nSession² · nTag / |N|`. -/
theorem basic_hash_unlinkability [AdmissibleDistinguishers] (F : K → N → T)
    (nTag nSession : ℕ) (q : TagReader.Port → ℕ) :
    ∀ εm εs, PRF.EUF F (Fin nTag) εm → PRF.EUF F (Fin nTag × Fin nSession) εs →
      Multiple.perPort F nTag nSession ≃[fun D =>
          εm (absorb (Multiple0.perLabel N T nTag nSession q) D) +
            εs (absorb (Single0.perLabel N T nTag nSession q) D) +
            ENNReal.ofReal ((nSession : ℝ) ^ 2 * nTag / Fintype.card N)]
        Single.perPort F nTag nSession := by
  -- `Multiple = Multiple0 • PRFs ≃ Multiple0 • EUF_RF`, and `Single0 • EUF_RF ≃ Single0 • PRFs =
  -- Single`; under the random functions the two protocols differ only once a tag repeats a
  -- nonce, of probability at most `nSession² · nTag / |N|`.
  sorry

/-- **The replay attack** [1, Appendix A]: with a tag, a session and two reader queries,
replaying an accepted message tells the protocol from the one that accepts each sent message
once. -/
theorem basic_hash_replay (F : K → N → T) (nTag nSession : ℕ) (q : TagReader.Port → ℕ)
    (tags : 0 < nTag) (sessions : 0 < nSession) (tagQuery : 1 ≤ q .tag)
    (readerQueries : 2 ≤ q .reader) :
    Δ (Multiple.perPort F nTag nSession (budget := q))
        (InjectiveAuth.perPort N T nTag • Multiple.perPort F nTag nSession) = 1 := by
  -- The distinguisher queries `tag(0)`, then `reader` twice on its message, and outputs whether
  -- the second reader query accepted: `1` on the protocol, `0` on the injective one.
  sorry

end

end ProofLadders.BasicHash
