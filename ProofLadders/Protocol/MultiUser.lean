import ProofLadders.Common.KeyExchange
import ProofLadders.Common.Programs

/-!
# Multi-user assumptions from single-user ones

Lemmas 1 and 2 of [1]: multi-user strong CDH with corruptions [1, Figure 2] from strong CDH
[1, Figure 1], losing `q₁ q₂`, or `q₁` without `Corrupt₂` and `q₂` without `Corrupt₁`; and
multi-user SUF-CMA with corruptions [1, Figure 4] from SUF-CMA [1, Figure 3], losing the number
`q` of users. The four notions are winning games (`StCDH.Single.game`, `StCDH.Multi.game`,
`SignatureScheme.SUFCMA.game` and `SignatureScheme.MultiSUFCMA.game` of `Common/KeyExchange`).

The adversaries `B` of the lemmas are the multi-user adversary with a reduction absorbed: a DSL
converter from the multi-user interface to the single-user one, which guesses the attacked
index, embeds the single-user challenge there and simulates the other indices with exponents or
key pairs it samples itself. It fetches the challenge (the public key) once and keeps it. A
corruption at a guessed index cannot be answered: the reduction stops, and then makes no inside
call and answers `⊥`. Without `Corrupt₂`, `StCDH.B.noCorrupt₂` guesses only `i*` and answers
every `Gen₂` with the challenge `g^y` rerandomized, `g^{y + r_j}`; without `Corrupt₁`,
symmetrically. In `StCDH.B`, the first `DDH` query on the challenge pair answered `1` is output
as the solution. In `SUFCMA.B`, the first verification at `j*` of a valid pair that `Sign` did not
output is output as the forgery, and every other verification is answered with the public key.

Each reduction is typed at amortized per-label inside budgets
(`Interface.Converter.ofAmortizedProgram`): per invocation it makes a bounded number of `DDH`
(signing) queries and samples, and a potential on its state, one at the challenge (the public
key) until it is fetched and one at the solution (the forgery) until it is output, pays for the
queries made once. Its single-user budget is that of [1]: one challenge, the `q_ddh` `DDH` queries
and one solution; one public key, the `q_sig` signing queries and one forgery.

Style: games.

## Main definitions

* `StCDH.B`, `StCDH.B.noCorrupt₂`, `StCDH.B.noCorrupt₁`, `SUFCMA.B`: the reductions, and their
  typings `.perLabel` at amortized per-label inside budgets
* `stCDHBudget`, `sufCMABudget`: the budgets of the single-user adversaries

## Main results

* `multi_stCDH_le`, `multi_stCDH_le_of_no_corrupt₂`, `multi_stCDH_le_of_no_corrupt₁`: Lemma 1
* `multi_sufCMA_le`: Lemma 2

## References

1. D. Riepel and P. Rösler. *Basic definitions, constructions, and proofs for unilateral
   authenticated key exchange*. The protocol ladder, `proof-ladders/protocol-ladder`,
   `Notes/computational/main.pdf`, 2025.
-/

namespace ProofLadders.MultiUser

open CategoryTheory ConstructiveCryptography Commons SystemAlgebra SystemAlgebra.DSL
  SystemAlgebra.Interface
open scoped SystemAlgebra SystemAlgebra.DSL

section StCDH

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- The budget of the St-CDH adversary of Lemma 1 [1]: one challenge, the `DDH` queries of the
multi-user adversary, and one solution. -/
def stCDHBudget (q : MultiStCDH.Port → ℕ) : SingleStCDH.Port → ℕ
  | .challenge => 1
  | .ddh => q .ddh
  | .solve => 1

noncomputable section

-- `B` of Lemma 1 [1]: `(i*, j*) ← [q₁] × [q₂]`; the challenge `(g^x, g^y)` is fetched once;
-- `Gen₁` answers its `i*`-th query with `g^x` and the others with `g^{x_i}` for `x_i ← ℤ_p`, and
-- `Gen₂` likewise with `g^y`; `Corrupt₁(i*)` and `Corrupt₂(j*)` stop; `DDH(X, Y, Z)` at `X = g^x`
-- is the inside `DDH`, whose first `1` at `Y = g^y` is output as the solution, and otherwise is
-- `[Z = Y^{x_i}]` at a known `x_i`, then `[Z = X^{y_j}]` at the first `j` with `Y = g^{y_j}`, the
-- inside `DDH` at `j*`.
converter StCDH.B(p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] : MultiStCDH G p q₁ q₂
  inside cdh : SingleStCDH G
  initialize
    (istar, jstar) ←$ 𝒰[Fin q₁ × Fin q₂]
    challenge ← ((1, 1) : G × G)
    fetched ← false
    solved ← false
    Xs ← ([] : List G)
    xs ← ([] : List (Option (ZMod p)))
    Ys ← ([] : List G)
    ys ← ([] : List (Option (ZMod p)))
    stopped ← false
  on gen₁() → Option G
    if stopped
      return none
    else
      if xs.length < q₁
        if xs.length = istar.val
          if !fetched
            challenge ← cdh.challenge()
            fetched ← true
          Xs ← Xs ++ [challenge.1]
          xs ← xs ++ [none]
          return some challenge.1
        else
          x ←$ 𝒰[ZMod p]
          Xs ← Xs ++ [g ^ x.val]
          xs ← xs ++ [some x]
          return some (g ^ x.val)
      else
        return none
  on gen₂() → Option G
    if stopped
      return none
    else
      if ys.length < q₂
        if ys.length = jstar.val
          if !fetched
            challenge ← cdh.challenge()
            fetched ← true
          Ys ← Ys ++ [challenge.2]
          ys ← ys ++ [none]
          return some challenge.2
        else
          y ←$ 𝒰[ZMod p]
          Ys ← Ys ++ [g ^ y.val]
          ys ← ys ++ [some y]
          return some (g ^ y.val)
      else
        return none
  on corrupt₁(i : Fin q₁) → Option (ZMod p)
    if stopped
      return none
    else
      match xs[i.val]?
      | none →
        return none
      | some none →
        stopped ← true
        return none
      | some (some x) →
        return some x
  on corrupt₂(j : Fin q₂) → Option (ZMod p)
    if stopped
      return none
    else
      match ys[j.val]?
      | none →
        return none
      | some none →
        stopped ← true
        return none
      | some (some y) →
        return some y
  on ddh(X : G, Y : G, Z : G) → Bool
    if stopped
      return false
    else
      if Xs[istar.val]? = some X
        d ← cdh.ddh(X, Y, Z)
        if d && decide (Ys[jstar.val]? = some Y) && !solved
          _correct ← cdh.solve(Z)
          solved ← true
          return true
        else
          return d
      else
        if xs.any fun entry => entry.any fun x => decide (X = g ^ x.val ∧ Z = Y ^ x.val)
          return true
        else
          match (List.finRange q₂).find? fun j => decide (Ys[j.val]? = some Y)
          | none →
            return false
          | some j →
            match ys[j.val]?
            | some (some y) →
              return decide (Z = X ^ y.val)
            | _ →
              d ← cdh.ddh(X, Y, Z)
              return d

-- `B` of Lemma 1 [1] without `Corrupt₂`: `i* ← [q₁]`; the challenge `(g^x, g^y)` is fetched once;
-- `Gen₁` as in `StCDH.B`; `Gen₂` answers `g^y · g^{r_j}` for `r_j ← ℤ_p`; `DDH(X, Y, Z)` at
-- `X = g^x` is the inside `DDH`, whose first `1` at `Y = g^y g^{r_j}` is output as
-- `Z · X^{-r_j}`, and otherwise is `[Z = Y^{x_i}]` at a known `x_i`, then the inside
-- `DDH(X, g^y, Z · X^{-r_j})` at the first `j` with `Y = g^y g^{r_j}`; `Corrupt₁(i*)` and
-- `Corrupt₂` stop.
converter StCDH.B.noCorrupt₂(p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₁] : MultiStCDH G p q₁ q₂
  inside cdh : SingleStCDH G
  initialize
    istar ←$ 𝒰[Fin q₁]
    challenge ← ((1, 1) : G × G)
    fetched ← false
    solved ← false
    Xs ← ([] : List G)
    xs ← ([] : List (Option (ZMod p)))
    Ys ← ([] : List G)
    rs ← ([] : List (ZMod p))
    stopped ← false
  on gen₁() → Option G
    if stopped
      return none
    else
      if xs.length < q₁
        if xs.length = istar.val
          if !fetched
            challenge ← cdh.challenge()
            fetched ← true
          Xs ← Xs ++ [challenge.1]
          xs ← xs ++ [none]
          return some challenge.1
        else
          x ←$ 𝒰[ZMod p]
          Xs ← Xs ++ [g ^ x.val]
          xs ← xs ++ [some x]
          return some (g ^ x.val)
      else
        return none
  on gen₂() → Option G
    if stopped
      return none
    else
      if rs.length < q₂
        if !fetched
          challenge ← cdh.challenge()
          fetched ← true
        r ←$ 𝒰[ZMod p]
        Ys ← Ys ++ [challenge.2 * g ^ r.val]
        rs ← rs ++ [r]
        return some (challenge.2 * g ^ r.val)
      else
        return none
  on corrupt₁(i : Fin q₁) → Option (ZMod p)
    if stopped
      return none
    else
      match xs[i.val]?
      | none →
        return none
      | some none →
        stopped ← true
        return none
      | some (some x) →
        return some x
  on corrupt₂(j : Fin q₂) → Option (ZMod p)
    if stopped
      return none
    else
      match rs[j.val]?
      | none →
        return none
      | some _ →
        stopped ← true
        return none
  on ddh(X : G, Y : G, Z : G) → Bool
    if stopped
      return false
    else
      if Xs[istar.val]? = some X
        d ← cdh.ddh(X, Y, Z)
        found ← (List.finRange q₂).find? fun j => decide (Ys[j.val]? = some Y)
        match if d && !solved then found.bind (fun j => rs[j.val]?) else none
        | some r →
          _correct ← cdh.solve(Z * (X ^ r.val)⁻¹)
          solved ← true
          return true
        | none →
          return d
      else
        if xs.any fun entry => entry.any fun x => decide (X = g ^ x.val ∧ Z = Y ^ x.val)
          return true
        else
          found ← (List.finRange q₂).find? fun j => decide (Ys[j.val]? = some Y)
          match found.bind fun j => rs[j.val]?
          | none →
            return false
          | some r →
            d ← cdh.ddh(X, Y * (g ^ r.val)⁻¹, Z * (X ^ r.val)⁻¹)
            return d

-- `B` of Lemma 1 [1] without `Corrupt₁`: `j* ← [q₂]`; the challenge `(g^x, g^y)` is fetched once;
-- `Gen₁` answers `g^x · g^{r_i}` for `r_i ← ℤ_p`; `Gen₂` as in `StCDH.B`; `DDH(X, Y, Z)` at the
-- first `i` with `X = g^x g^{r_i}` is the inside `DDH(g^x, Y, Z · Y^{-r_i})`, whose first `1` at
-- `Y = g^y` is output as `Z · Y^{-r_i}`, and otherwise is `[Z = X^{y_j}]` at the first `j` with
-- `Y = g^{y_j}`, the inside `DDH` at `j*`; `Corrupt₁` and `Corrupt₂(j*)` stop.
converter StCDH.B.noCorrupt₁(p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₂] : MultiStCDH G p q₁ q₂
  inside cdh : SingleStCDH G
  initialize
    jstar ←$ 𝒰[Fin q₂]
    challenge ← ((1, 1) : G × G)
    fetched ← false
    solved ← false
    Xs ← ([] : List G)
    rs ← ([] : List (ZMod p))
    Ys ← ([] : List G)
    ys ← ([] : List (Option (ZMod p)))
    stopped ← false
  on gen₁() → Option G
    if stopped
      return none
    else
      if rs.length < q₁
        if !fetched
          challenge ← cdh.challenge()
          fetched ← true
        r ←$ 𝒰[ZMod p]
        Xs ← Xs ++ [challenge.1 * g ^ r.val]
        rs ← rs ++ [r]
        return some (challenge.1 * g ^ r.val)
      else
        return none
  on gen₂() → Option G
    if stopped
      return none
    else
      if ys.length < q₂
        if ys.length = jstar.val
          if !fetched
            challenge ← cdh.challenge()
            fetched ← true
          Ys ← Ys ++ [challenge.2]
          ys ← ys ++ [none]
          return some challenge.2
        else
          y ←$ 𝒰[ZMod p]
          Ys ← Ys ++ [g ^ y.val]
          ys ← ys ++ [some y]
          return some (g ^ y.val)
      else
        return none
  on corrupt₁(i : Fin q₁) → Option (ZMod p)
    if stopped
      return none
    else
      match rs[i.val]?
      | none →
        return none
      | some _ →
        stopped ← true
        return none
  on corrupt₂(j : Fin q₂) → Option (ZMod p)
    if stopped
      return none
    else
      match ys[j.val]?
      | none →
        return none
      | some none →
        stopped ← true
        return none
      | some (some y) →
        return some y
  on ddh(X : G, Y : G, Z : G) → Bool
    if stopped
      return false
    else
      found ← (List.finRange q₁).find? fun i => decide (Xs[i.val]? = some X)
      match found.bind fun i => rs[i.val]?
      | some r →
        d ← cdh.ddh(X * (g ^ r.val)⁻¹, Y, Z * (Y ^ r.val)⁻¹)
        if d && decide (Ys[jstar.val]? = some Y) && !solved
          _correct ← cdh.solve(Z * (Y ^ r.val)⁻¹)
          solved ← true
          return true
        else
          return d
      | none →
        match (List.finRange q₂).find? fun j => decide (Ys[j.val]? = some Y)
        | none →
          return false
        | some j →
          match ys[j.val]?
          | some (some y) →
            return decide (Z = X ^ y.val)
          | _ →
            d ← cdh.ddh(X, Y, Z)
            return d

/-- The inside calls of `StCDH.B` per procedure: `DDH` from `DDH`, the guess, and the exponents of
the generations. -/
def StCDH.B.calls : MultiStCDH.Port → SingleStCDH.Port ⊕ (Unit ⊕ (Unit ⊕ Unit)) → ℕ
  | .ddh, .inl .ddh => 1
  | _, .inr (.inl _) => 1
  | .gen₁, .inr (.inr (.inl _)) => 1
  | .gen₂, .inr (.inr (.inr _)) => 1
  | _, _ => 0

/-- The single-user queries of `StCDH.B` made once and not yet made: the challenge until it is
fetched, and the solution until it is output. -/
def StCDH.B.once (fetched solved : Bool) : SingleStCDH.Port ⊕ (Unit ⊕ (Unit ⊕ Unit)) → ℕ
  | .inl .challenge => if fetched then 0 else 1
  | .inl .solve => if solved then 0 else 1
  | _ => 0

/-- The potential of `StCDH.B`: its single-user queries made once and not yet made. -/
def StCDH.B.potential (p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] :
    Option (TypeOf (StCDH.B.initial p g q₁ q₂)) → SingleStCDH.Port ⊕ (Unit ⊕ (Unit ⊕ Unit)) → ℕ
  | none => StCDH.B.once false false
  | some (_, _, _, fetched, solved, _) => StCDH.B.once fetched solved

/-- `StCDH.B` calls each inside label at most `StCDH.B.calls` times per procedure, and the
challenge and the solution once, paid by `StCDH.B.potential`. -/
lemma StCDH.B.labelBounded (p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] :
    (StCDH.B.body p g q₁ q₂).LabelBoundedWith StCDH.B.calls (StCDH.B.potential p g q₁ q₂) := by
  intro s o u
  cases o <;> simp only [StCDH.B.body] <;> cases s <;> dsimp only <;>
    repeat' (first
      | exact Program.labelCallBoundWith_return _ (by
          intro j; rcases j with (_ | _ | _) | _ | _ | _ <;>
            simp [StCDH.B.calls, StCDH.B.potential, StCDH.B.once])
      | (refine Program.labelCallBoundWith_call _ _ _
          (by simp_all [StCDH.B.calls, StCDH.B.potential, StCDH.B.once]) fun y => ?_)
      | split)

/-- The inside interface of the program of `StCDH.B`: the St-CDH game beside the sources. -/
abbrev StCDH.B.inside (p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
    (q : MultiStCDH.Port → ℕ) : Interface :=
  (SingleStCDH.perPort G (stCDHBudget q)).tensor
    ((Interface.source (lawType (StCDH.B.law1 p g q₁ q₂)) (∑ i, q i)).tensor
      ((Interface.source (lawType (StCDH.B.law2 p g q₁ q₂)) (∑ i, q i)).tensor
        (Interface.source (lawType (StCDH.B.law3 p g q₁ q₂)) (∑ i, q i))))

omit [DecidableEq G] in
/-- The inside interface admits the amortized per-label budget of `StCDH.B`. -/
lemma StCDH.B.admits (p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
    (q : MultiStCDH.Port → ℕ) :
    (StCDH.B.inside p g q₁ q₂ q).AdmitsLabelBudget
      fun j => ∑ o, StCDH.B.calls o j * q o + StCDH.B.potential p g q₁ q₂ none j := by
  refine ((portBudget_admitsLabelBudget _ _ _ _).tensor
    ((queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simp)).tensor
      ((queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simp)).tensor
        (queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simp))))).mono
    fun j => ?_
  rcases j with (_ | _ | _) | _ | _ | _ <;>
    simp [Finset.univ, Fintype.elems, StCDH.B.calls, StCDH.B.potential, StCDH.B.once,
      stCDHBudget]
  all_goals omega

/-- **`B` of Lemma 1 at per-port budgets**: the program of `StCDH.B` at the per-label call bound
`StCDH.B.calls` with the potential `StCDH.B.potential`, beside its sources. -/
def StCDH.B.perLabel (p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
    (q : MultiStCDH.Port → ℕ) :
    MultiStCDH.perPort G p q₁ q₂ q ⟶ SingleStCDH.perPort G (stCDHBudget q) :=
  Converter.ofAmortizedProgram (A := MultiStCDH.perPort G p q₁ q₂ q)
      (B := StCDH.B.inside p g q₁ q₂ q) none (StCDH.B.body p g q₁ q₂)
      (StCDH.B.bound_spec p g q₁ q₂) StCDH.B.calls (StCDH.B.potential p g q₁ q₂)
      (StCDH.B.labelBounded p g q₁ q₂) q (fun _ hd => hd.2) (StCDH.B.admits p g q₁ q₂ q) ≫
    Interface.rightContext _ (StCDH.B.randomness p g q₁ q₂ (∑ i, q i))

/-- The potential of `StCDH.B.noCorrupt₂`: its single-user queries made once and not yet made. -/
def StCDH.B.noCorrupt₂.potential (p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₁] :
    Option (TypeOf (StCDH.B.noCorrupt₂.initial p g q₁ q₂)) →
      SingleStCDH.Port ⊕ (Unit ⊕ (Unit ⊕ Unit)) → ℕ
  | none => StCDH.B.once false false
  | some (_, _, fetched, solved, _) => StCDH.B.once fetched solved

/-- `StCDH.B.noCorrupt₂` calls each inside label at most `StCDH.B.calls` times per procedure, and
the challenge and the solution once, paid by `StCDH.B.noCorrupt₂.potential`. -/
lemma StCDH.B.noCorrupt₂.labelBounded (p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₁] :
    (StCDH.B.noCorrupt₂.body p g q₁ q₂).LabelBoundedWith StCDH.B.calls
      (StCDH.B.noCorrupt₂.potential p g q₁ q₂) := by
  intro s o u
  cases o <;> simp only [StCDH.B.noCorrupt₂.body] <;> cases s <;> dsimp only <;>
    repeat' (first
      | exact Program.labelCallBoundWith_return _ (by
          intro j; rcases j with (_ | _ | _) | _ | _ | _ <;>
            simp [StCDH.B.calls, StCDH.B.noCorrupt₂.potential, StCDH.B.once])
      | (refine Program.labelCallBoundWith_call _ _ _
          (by simp_all [StCDH.B.calls, StCDH.B.noCorrupt₂.potential, StCDH.B.once])
          fun y => ?_)
      | split)

/-- The inside interface of the program of `StCDH.B.noCorrupt₂`. -/
abbrev StCDH.B.noCorrupt₂.inside (p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₁]
    (q : MultiStCDH.Port → ℕ) : Interface :=
  (SingleStCDH.perPort G (stCDHBudget q)).tensor
    ((Interface.source (lawType (StCDH.B.noCorrupt₂.law1 p g q₁ q₂)) (∑ i, q i)).tensor
      ((Interface.source (lawType (StCDH.B.noCorrupt₂.law2 p g q₁ q₂)) (∑ i, q i)).tensor
        (Interface.source (lawType (StCDH.B.noCorrupt₂.law3 p g q₁ q₂)) (∑ i, q i))))

omit [DecidableEq G] in
/-- The inside interface admits the amortized per-label budget of `StCDH.B.noCorrupt₂`. -/
lemma StCDH.B.noCorrupt₂.admits (p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₁]
    (q : MultiStCDH.Port → ℕ) :
    (StCDH.B.noCorrupt₂.inside p g q₁ q₂ q).AdmitsLabelBudget
      fun j => ∑ o, StCDH.B.calls o j * q o + StCDH.B.noCorrupt₂.potential p g q₁ q₂ none j := by
  refine ((portBudget_admitsLabelBudget _ _ _ _).tensor
    ((queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simp)).tensor
      ((queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simp)).tensor
        (queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simp))))).mono
    fun j => ?_
  rcases j with (_ | _ | _) | _ | _ | _ <;>
    simp [Finset.univ, Fintype.elems, StCDH.B.calls, StCDH.B.noCorrupt₂.potential,
      StCDH.B.once, stCDHBudget]
  all_goals omega

/-- **`B` of Lemma 1 without `Corrupt₂` at per-port budgets.** -/
def StCDH.B.noCorrupt₂.perLabel (p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₁]
    (q : MultiStCDH.Port → ℕ) :
    MultiStCDH.perPort G p q₁ q₂ q ⟶ SingleStCDH.perPort G (stCDHBudget q) :=
  Converter.ofAmortizedProgram (A := MultiStCDH.perPort G p q₁ q₂ q)
      (B := StCDH.B.noCorrupt₂.inside p g q₁ q₂ q) none (StCDH.B.noCorrupt₂.body p g q₁ q₂)
      (StCDH.B.noCorrupt₂.bound_spec p g q₁ q₂) StCDH.B.calls
      (StCDH.B.noCorrupt₂.potential p g q₁ q₂) (StCDH.B.noCorrupt₂.labelBounded p g q₁ q₂) q
      (fun _ hd => hd.2) (StCDH.B.noCorrupt₂.admits p g q₁ q₂ q) ≫
    Interface.rightContext _ (StCDH.B.noCorrupt₂.randomness p g q₁ q₂ (∑ i, q i))

/-- The potential of `StCDH.B.noCorrupt₁`: its single-user queries made once and not yet made. -/
def StCDH.B.noCorrupt₁.potential (p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₂] :
    Option (TypeOf (StCDH.B.noCorrupt₁.initial p g q₁ q₂)) →
      SingleStCDH.Port ⊕ (Unit ⊕ (Unit ⊕ Unit)) → ℕ
  | none => StCDH.B.once false false
  | some (_, _, fetched, solved, _) => StCDH.B.once fetched solved

/-- `StCDH.B.noCorrupt₁` calls each inside label at most `StCDH.B.calls` times per procedure, and
the challenge and the solution once, paid by `StCDH.B.noCorrupt₁.potential`. -/
lemma StCDH.B.noCorrupt₁.labelBounded (p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₂] :
    (StCDH.B.noCorrupt₁.body p g q₁ q₂).LabelBoundedWith StCDH.B.calls
      (StCDH.B.noCorrupt₁.potential p g q₁ q₂) := by
  intro s o u
  cases o <;> simp only [StCDH.B.noCorrupt₁.body] <;> cases s <;> dsimp only <;>
    repeat' (first
      | exact Program.labelCallBoundWith_return _ (by
          intro j; rcases j with (_ | _ | _) | _ | _ | _ <;>
            simp [StCDH.B.calls, StCDH.B.noCorrupt₁.potential, StCDH.B.once])
      | (refine Program.labelCallBoundWith_call _ _ _
          (by simp_all [StCDH.B.calls, StCDH.B.noCorrupt₁.potential, StCDH.B.once])
          fun y => ?_)
      | split)

/-- The inside interface of the program of `StCDH.B.noCorrupt₁`. -/
abbrev StCDH.B.noCorrupt₁.inside (p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₂]
    (q : MultiStCDH.Port → ℕ) : Interface :=
  (SingleStCDH.perPort G (stCDHBudget q)).tensor
    ((Interface.source (lawType (StCDH.B.noCorrupt₁.law1 p g q₁ q₂)) (∑ i, q i)).tensor
      ((Interface.source (lawType (StCDH.B.noCorrupt₁.law2 p g q₁ q₂)) (∑ i, q i)).tensor
        (Interface.source (lawType (StCDH.B.noCorrupt₁.law3 p g q₁ q₂)) (∑ i, q i))))

omit [DecidableEq G] in
/-- The inside interface admits the amortized per-label budget of `StCDH.B.noCorrupt₁`. -/
lemma StCDH.B.noCorrupt₁.admits (p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₂]
    (q : MultiStCDH.Port → ℕ) :
    (StCDH.B.noCorrupt₁.inside p g q₁ q₂ q).AdmitsLabelBudget
      fun j => ∑ o, StCDH.B.calls o j * q o + StCDH.B.noCorrupt₁.potential p g q₁ q₂ none j := by
  refine ((portBudget_admitsLabelBudget _ _ _ _).tensor
    ((queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simp)).tensor
      ((queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simp)).tensor
        (queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simp))))).mono
    fun j => ?_
  rcases j with (_ | _ | _) | _ | _ | _ <;>
    simp [Finset.univ, Fintype.elems, StCDH.B.calls, StCDH.B.noCorrupt₁.potential,
      StCDH.B.once, stCDHBudget]
  all_goals omega

/-- **`B` of Lemma 1 without `Corrupt₁` at per-port budgets.** -/
def StCDH.B.noCorrupt₁.perLabel (p : ℕ) [NeZero p] (g : G) (q₁ q₂ : ℕ) [NeZero q₂]
    (q : MultiStCDH.Port → ℕ) :
    MultiStCDH.perPort G p q₁ q₂ q ⟶ SingleStCDH.perPort G (stCDHBudget q) :=
  Converter.ofAmortizedProgram (A := MultiStCDH.perPort G p q₁ q₂ q)
      (B := StCDH.B.noCorrupt₁.inside p g q₁ q₂ q) none (StCDH.B.noCorrupt₁.body p g q₁ q₂)
      (StCDH.B.noCorrupt₁.bound_spec p g q₁ q₂) StCDH.B.calls
      (StCDH.B.noCorrupt₁.potential p g q₁ q₂) (StCDH.B.noCorrupt₁.labelBounded p g q₁ q₂) q
      (fun _ hd => hd.2) (StCDH.B.noCorrupt₁.admits p g q₁ q₂ q) ≫
    Interface.rightContext _ (StCDH.B.noCorrupt₁.randomness p g q₁ q₂ (∑ i, q i))

end

/-- **Lemma 1** of [1]: for a group of prime order `p` generated by `g`, every solver of
`(q₁, q₂)`-St-CDH wins with at most `q₁ q₂` times its probability of winning St-CDH with `B`
attached. -/
theorem multi_stCDH_le (p : ℕ) [NeZero p] (g : G) (order : Fintype.card G = p)
    (prime : p.Prime) (generator : Subgroup.zpowers g = ⊤) (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
    (q : MultiStCDH.Port → ℕ) :
    ∀ s ∈ CompatibleSolverClass.solvers (MultiStCDH.perPort G p q₁ q₂ q),
      s.2 (StCDH.Multi.game p g q₁ q₂ q) ≤
        q₁ * q₂ * s.2 (StCDH.B.perLabel p g q₁ q₂ q • StCDH.Single.game p g (stCDHBudget q)) := by
  -- Until the winning query, the views agree unless `i*` or `j*` is corrupted, and the
  -- simulated `DDH` is the real one by `order`; the winning pair is `(i*, j*)` with probability
  -- `1/(q₁ q₂)`, independently of the view, and then the winning query is the first `DDH` query
  -- on the challenge pair answered `1`, which `B` outputs as the solution.
  sorry

/-- **Lemma 1** of [1], without `Corrupt₂`: losing `q₁`. -/
theorem multi_stCDH_le_of_no_corrupt₂ (p : ℕ) [NeZero p] (g : G) (order : Fintype.card G = p)
    (prime : p.Prime) (generator : Subgroup.zpowers g = ⊤) (q₁ q₂ : ℕ) [NeZero q₁]
    (q : MultiStCDH.Port → ℕ) (noCorrupt : q .corrupt₂ = 0) :
    ∀ s ∈ CompatibleSolverClass.solvers (MultiStCDH.perPort G p q₁ q₂ q),
      s.2 (StCDH.Multi.game p g q₁ q₂ q) ≤
        q₁ * s.2 (StCDH.B.noCorrupt₂.perLabel p g q₁ q₂ q •
          StCDH.Single.game p g (stCDHBudget q)) := by
  -- The rerandomized `g^{y + r_j}` are uniform and independent, and `DDH` on them is the inside
  -- `DDH` on `(X, g^y, Z X^{-r_j})`, by `order`; the winning `i` is `i*` with probability
  -- `1/q₁`, and then `Z X^{-r_j} = g^{xy}`.
  sorry

/-- **Lemma 1** of [1], without `Corrupt₁`: losing `q₂`. -/
theorem multi_stCDH_le_of_no_corrupt₁ (p : ℕ) [NeZero p] (g : G) (order : Fintype.card G = p)
    (prime : p.Prime) (generator : Subgroup.zpowers g = ⊤) (q₁ q₂ : ℕ) [NeZero q₂]
    (q : MultiStCDH.Port → ℕ) (noCorrupt : q .corrupt₁ = 0) :
    ∀ s ∈ CompatibleSolverClass.solvers (MultiStCDH.perPort G p q₁ q₂ q),
      s.2 (StCDH.Multi.game p g q₁ q₂ q) ≤
        q₂ * s.2 (StCDH.B.noCorrupt₁.perLabel p g q₁ q₂ q •
          StCDH.Single.game p g (stCDHBudget q)) := by
  -- Symmetric: the rerandomized `g^{x + r_i}`, and the winning `j` is `j*` with probability
  -- `1/q₂`.
  sorry

end StCDH

section Signature

variable {PK SK M Sig : Type} [Fintype PK] [Fintype SK] [Fintype M] [Fintype Sig]

/-- The budget of the SUF-CMA adversary of Lemma 2 [1]: one public key, the signing queries of
the multi-user adversary, and one forgery. -/
def sufCMABudget (q : MultiSigning.Port → ℕ) : Signing.Port → ℕ
  | .publicKey => 1
  | .sign => q .sign
  | .verify => 1

noncomputable section

-- `B` of Lemma 2 [1]: `j* ← [q]`; `Gen` answers its `j*`-th query with the public key `pk` and
-- the others with `pk_j` for `(pk_j, sk_j) ← SIG.gen`; `Sign(j, m)` is the inside `Sign(m)` at
-- `j*`, recorded in `Q`, and `SIG.sig(sk_j, m)` otherwise; `Corrupt(j*)` stops; `verify(j, m, σ)`
-- is `SIG.vfy(pk_j, m, σ)`, and its first `1` at `j*` on a pair not in `Q` is output as the
-- forgery, the inside verification.
converter SUFCMA.B(scheme : SignatureScheme PK SK M Sig) (users : ℕ) [NeZero users] [DecidableEq SK] [DecidableEq M] [DecidableEq Sig] : MultiSigning PK SK M Sig users
  inside signing : Signing PK M Sig
  initialize
    jstar ←$ 𝒰[Fin users]
    keys ← ([] : List (PK × Option SK))
    Q ← ([] : List (M × Sig))
    forged ← false
    stopped ← false
  on gen() → Option PK
    if stopped
      return none
    else
      if keys.length < users
        if keys.length = jstar.val
          pk ← signing.publicKey()
          keys ← keys ++ [(pk, none)]
          return some pk
        else
          key ←$ scheme.gen
          keys ← keys ++ [(key.1, some key.2)]
          return some key.1
      else
        return none
  on sign(j : Fin users, m : M) → Option Sig
    if stopped
      return none
    else
      match keys[j.val]?
      | none →
        return none
      | some (_, none) →
        σ ← signing.sign(m)
        Q ← Q ++ [(m, σ)]
        return some σ
      | some (_, some sk) →
        signatures ←$ scheme.signatures
        return some (signatures (sk, m))
  on corrupt(j : Fin users) → Option SK
    if stopped
      return none
    else
      match keys[j.val]?
      | none →
        return none
      | some (_, none) →
        stopped ← true
        return none
      | some (_, some sk) →
        return some sk
  on verify(j : Fin users, m : M, σ : Sig) → Bool
    if stopped
      return false
    else
      match keys[j.val]?
      | none →
        return false
      | some (pk, none) →
        if !forged && scheme.verify pk m σ && decide ((m, σ) ∉ Q)
          valid ← signing.verify(m, σ)
          forged ← true
          return valid
        else
          return scheme.verify pk m σ
      | some (pk, some _) →
        return scheme.verify pk m σ

/-- The inside calls of `SUFCMA.B` per procedure: signing from `Sign`, the guess, and the key
pairs and signatures it samples. -/
def SUFCMA.B.calls : MultiSigning.Port → Signing.Port ⊕ (Unit ⊕ (Unit ⊕ Unit)) → ℕ
  | .sign, .inl .sign => 1
  | _, .inr (.inl _) => 1
  | .gen, .inr (.inr (.inl _)) => 1
  | .sign, .inr (.inr (.inr _)) => 1
  | _, _ => 0

/-- The potential of `SUFCMA.B`: its single-user queries made once and not yet made, the public
key until the key of `j*` is generated, and the forgery until it is output. -/
def SUFCMA.B.potential [DecidableEq SK] [DecidableEq M] [DecidableEq Sig]
    (scheme : SignatureScheme PK SK M Sig) (users : ℕ) [NeZero users] :
    Option (TypeOf (SUFCMA.B.initial scheme users)) → Signing.Port ⊕ (Unit ⊕ (Unit ⊕ Unit)) → ℕ
  | none, .inl .publicKey | none, .inl .verify => 1
  | some (jstar, keys, _), .inl .publicKey => if jstar.val < keys.length then 0 else 1
  | some (_, _, _, forged, _), .inl .verify => if forged then 0 else 1
  | _, _ => 0

/-- `SUFCMA.B` calls each inside label at most `SUFCMA.B.calls` times per procedure, and the
public key and the forgery once, paid by `SUFCMA.B.potential`. -/
lemma SUFCMA.B.labelBounded [DecidableEq SK] [DecidableEq M] [DecidableEq Sig]
    (scheme : SignatureScheme PK SK M Sig) (users : ℕ) [NeZero users] :
    (SUFCMA.B.body scheme users).LabelBoundedWith SUFCMA.B.calls
      (SUFCMA.B.potential scheme users) := by
  intro s o u
  cases o <;> simp only [SUFCMA.B.body] <;> cases s <;> dsimp only <;>
    repeat' (first
      | exact Program.labelCallBoundWith_return _ (by
          intro j; rcases j with (_ | _ | _) | _ | _ | _ <;>
            simp_all [SUFCMA.B.calls, SUFCMA.B.potential] <;> (try split_ifs) <;> omega)
      | (refine Program.labelCallBoundWith_call _ _ _
          (by simp_all [SUFCMA.B.calls, SUFCMA.B.potential]) fun y => ?_)
      | split)

/-- The inside interface of the program of `SUFCMA.B`: the SUF-CMA game beside the sources. -/
abbrev SUFCMA.B.inside [DecidableEq SK] [DecidableEq M] [DecidableEq Sig]
    (scheme : SignatureScheme PK SK M Sig) (users : ℕ) [NeZero users]
    (q : MultiSigning.Port → ℕ) : Interface :=
  (Signing.perPort PK M Sig (sufCMABudget q)).tensor
    ((Interface.source (lawType (SUFCMA.B.law1 scheme users)) (∑ i, q i)).tensor
      ((Interface.source (lawType (SUFCMA.B.law2 scheme users)) (∑ i, q i)).tensor
        (Interface.source (lawType (SUFCMA.B.law3 scheme users)) (∑ i, q i))))

/-- The inside interface admits the amortized per-label budget of `SUFCMA.B`. -/
lemma SUFCMA.B.admits [DecidableEq SK] [DecidableEq M] [DecidableEq Sig]
    (scheme : SignatureScheme PK SK M Sig) (users : ℕ) [NeZero users]
    (q : MultiSigning.Port → ℕ) :
    (SUFCMA.B.inside scheme users q).AdmitsLabelBudget
      fun j => ∑ o, SUFCMA.B.calls o j * q o + SUFCMA.B.potential scheme users none j := by
  refine ((portBudget_admitsLabelBudget _ _ _ _).tensor
    ((queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simp)).tensor
      ((queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simp)).tensor
        (queryBudget_admitsLabelBudget _ _ _ (fun _ => ∑ i, q i) (by simp))))).mono
    fun j => ?_
  rcases j with (_ | _ | _) | _ | _ | _ <;>
    simp [Finset.univ, Fintype.elems, SUFCMA.B.calls, SUFCMA.B.potential, sufCMABudget]
  all_goals omega

/-- **`B` of Lemma 2 at per-port budgets**: the program of `SUFCMA.B` at the per-label call bound
`SUFCMA.B.calls` with the potential `SUFCMA.B.potential`, beside its sources. -/
def SUFCMA.B.perLabel [DecidableEq SK] [DecidableEq M] [DecidableEq Sig]
    (scheme : SignatureScheme PK SK M Sig) (users : ℕ) [NeZero users]
    (q : MultiSigning.Port → ℕ) :
    MultiSigning.perPort PK SK M Sig users q ⟶ Signing.perPort PK M Sig (sufCMABudget q) :=
  Converter.ofAmortizedProgram (A := MultiSigning.perPort PK SK M Sig users q)
      (B := SUFCMA.B.inside scheme users q) none (SUFCMA.B.body scheme users)
      (SUFCMA.B.bound_spec scheme users) SUFCMA.B.calls (SUFCMA.B.potential scheme users)
      (SUFCMA.B.labelBounded scheme users) q (fun _ hd => hd.2) (SUFCMA.B.admits scheme users q) ≫
    Interface.rightContext _ (SUFCMA.B.randomness scheme users (∑ i, q i))

end

/-- **Lemma 2** of [1]: every solver of `q`-SUF-CMA, for `users` users, wins with at most `users`
times its probability of winning SUF-CMA with `B` attached. -/
theorem multi_sufCMA_le [DecidableEq SK] [DecidableEq M] [DecidableEq Sig]
    (scheme : SignatureScheme PK SK M Sig) (users : ℕ) [NeZero users]
    (q : MultiSigning.Port → ℕ) :
    ∀ s ∈ CompatibleSolverClass.solvers (MultiSigning.perPort PK SK M Sig users q),
      s.2 (SignatureScheme.MultiSUFCMA.game scheme users q) ≤
        users * s.2 (SUFCMA.B.perLabel scheme users q •
          SignatureScheme.SUFCMA.game scheme (sufCMABudget q)) := by
  -- Until the forgery, the views agree unless `j*` is corrupted, and a verification answered with
  -- the public key is the real one; the forging user is `j*` with probability `1/users`,
  -- independently of the view, and then the forgery is the first verification at `j*` of a valid
  -- pair not in `Q`, which `B` outputs.
  sorry

end Signature

end ProofLadders.MultiUser
