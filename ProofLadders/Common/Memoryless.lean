import ProofLadders.Common.ProbAutomaton
import Commons.Definitions.Ideal

/-!
# Memoryless systems

A system is memoryless when the law of its reply depends only on the current query, never on the
history [1, Definition 3.1, §3.6.1]. Being memoryless is independent of the interface: a source
(trigger inputs) can be memoryless or have memory [1, Definition 3.1], and so can a system with
inputs. As a random system, a memoryless system is given by its conditional reply laws, which are
those of the current query alone.

A probabilistic automaton whose reply law does not depend on its state is memoryless, and a
program run against memoryless replies replies memorylessly, with the law of one invocation fed
with fresh samples of the inside laws. So attaching the converter of such a program to a
memoryless system gives a memoryless system:

```
        x            ┌───┐  inside queries   ┌──────────┐
  ──────────────────►│ 𝓡 ├──────────────────►│  mem(ν)  │      =      mem(κ)
  ◄──────────────────┤   │◄──────────────────┤          │
     y ~ κ(x)        └───┘  fresh samples    └──────────┘     κ = 𝓡's reply law against ν
```

Equalities of systems built this way are equalities of reply laws.

Upstream candidates (trailofbits/constructive-cryptography#11): `RandomSystem.memoryless`,
`RandomSystem.portLaw`, `ProbStep.Memoryless`, `RandomSystem.ofProbAutomaton_eq_memoryless`,
`Program.replyLaw`, `Program.memoryless_probCombine`, for `RandomSystems`; the composition laws
`Interface.Converter.*_smul_memoryless`, for the typed systems; `MemorylessSource`, for
`Commons.Definitions.Ideal`.

## Main definitions

* `RandomSystem.memoryless D ν`: the memoryless system with the reply law `ν` on the domain `D`
* `RandomSystem.portLaw ν`: the reply law `ν i x` at the queried port `i`
* `ProbStep.Memoryless step ν`: a probabilistic step replying with the law `ν` from every state
* `Program.replyLaw P ν`: the reply law of an invocation against inside replies of the laws `ν`
* `MemorylessSource Y ν`: the DSL source `y ←$ ν; return y`

## Main results

* `RandomSystem.ofProbAutomaton_eq_memoryless`: an automaton with a memoryless step is the
  memoryless system of its reply law
* `Program.memoryless_probCombine`: a program against a memoryless step is memoryless
* `FreshSampling.memoryless_eq`: a system presented as memoryless fresh sampling is the
  memoryless system
* `Interface.Converter.ofProgram_smul_memoryless`,
  `Interface.Converter.ofPreservingProgram_smul_memoryless`,
  `Interface.Converter.ofPreservingProgram_comp_rightContext_smul_memoryless`: the composition
  law `𝓡 • mem(ν) = mem(κ)`
* `MemorylessSource.memoryless_eq`: the DSL source of `ν` is the memoryless system of `ν`

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

namespace SystemAlgebra

open Probability Probability.Distribution Classical

/-! ## Random systems -/

namespace RandomSystem

variable {A B : Type} [Fintype A] [Fintype B]

/-- **The memoryless system** with the reply law `ν` [1, Definition 3.1, §3.6.1]: on the domain
`D`, the reply to the query `x` is a fresh sample of `ν x`, independent of the history. -/
noncomputable def memoryless (D : Domain A B) (ν : A → ProbDist B) : RandomSystem A B D :=
  -- A random system is given by its conditional reply laws (`ofConditional`). Here the law at
  -- history `h` and query `x` ignores `h`: it is `ν x`.
  ofConditional fun _ x _ => ν x

/-- **The chain rule**: one more exchange multiplies the probability of a transcript by the
reply law, when the domain admits the query. -/
lemma memoryless_snoc (D : Domain A B) (ν : A → ProbDist B) (h : List (A × B)) (x : A)
    (y : B) :
    memoryless D ν (h ++ [(x, y)]) = if D h x then memoryless D ν h * (ν x).1 y else 0 := by
  -- `ofConditional_snoc` is the chain rule of any system given by conditional laws ...
  have chain := ofConditional_snoc (D := D) (fun _ x _ => ν x) h x y
  -- ... stated with a dependent `if` (`dite`); ours does not use the proof of `D h x`
  rw [dite_eq_ite] at chain
  exact chain

variable {I : Type} {X Y : I → Type}

/-- **The reply law at the queried port**: for a query `x` at the port `i`, the law `ν i x` of
the reply, as a law on replies tagged with their port. -/
noncomputable def portLaw (ν : ∀ i, X i → ProbDist (Y i)) (x : Σ i, X i) :
    ProbDist (Σ i, Y i) :=
  ProbDist.map (Sigma.mk x.1) (ν x.1 x.2)

end RandomSystem

namespace ProbStep

variable {S I : Type} {X Y : I → Type}

/-- **A memoryless step** with the reply law `ν`: from every state, the reply to `x` at `i` has
the law `ν i x`. -/
def Memoryless (step : ProbStep S I X Y) (ν : ∀ i, X i → ProbDist (Y i)) : Prop :=
  -- `step s i x` is a law on pairs (next state, reply); forgetting the next state leaves `ν i x`
  ∀ s i x, fTransform Prod.snd (step s i x).1 = (ν i x).1

/-- From any state, a memoryless step replies `y` with the probability its reply law gives `y`. -/
lemma Memoryless.mass_outcome {step : ProbStep S I X Y} {ν : ∀ i, X i → ProbDist (Y i)}
    (hν : step.Memoryless ν) (s : S) (x : Σ i, X i) (y : Σ i, Y i) :
    (step.outcome s x).mass (·.2 = y) = (RandomSystem.portLaw ν x).1 y := by
  -- The probability that the reply is `y` is the pushforward to the reply, evaluated at `y`.
  rw [← fTransform_apply_eq_mass]
  -- `outcome` is the step at port `x.1`, with the reply tagged by the port: (next, ⟨x.1, reply⟩)
  rw [outcome, fTransform_fTransform]
  -- Tagging and then keeping the reply = keeping the reply and then tagging it.
  rw [show (Prod.snd ∘ tagged x) = Sigma.mk x.1 ∘ Prod.snd from rfl, ← fTransform_fTransform]
  -- The step is memoryless: its reply law is `ν x.1 x.2`, whatever the state `s`.
  rw [hν s x.1 x.2]
  -- What remains is the definition of `portLaw`.
  rfl

/-- **Fresh samples are memoryless.** -/
lemma memoryless_fresh {Z : Type} (law : ProbDist Z) :
    (fresh law).Memoryless fun _ _ => law := by
  intro _ _ _
  -- `fresh law` keeps its (trivial) state and replies with a new sample of `law`:
  --   law on (state, reply) = law pushed along z ↦ ((), z)
  -- Keeping the reply composes this map with `Prod.snd`, which is the identity on samples.
  simp only [fresh, fTransform_fTransform]
  exact fTransform_id _

variable {T J : Type} {X₁ Y₁ : I → Type} {X₂ Y₂ : J → Type}

/-- The reply laws of two steps side by side: a query on the left port gets the left law, one on
the right port the right law. -/
def parallelLaw (ν₁ : ∀ i, X₁ i → ProbDist (Y₁ i)) (ν₂ : ∀ j, X₂ j → ProbDist (Y₂ j)) :
    ∀ l : I ⊕ J, Sum.rec (motive := fun _ => Type) X₁ X₂ l →
      ProbDist (Sum.rec (motive := fun _ => Type) Y₁ Y₂ l)
  | .inl i, x => ν₁ i x
  | .inr j, x => ν₂ j x

/-- **Memoryless steps side by side are memoryless.** -/
lemma Memoryless.parallel {f : ProbStep S I X₁ Y₁} {g : ProbStep T J X₂ Y₂}
    {ν₁ : ∀ i, X₁ i → ProbDist (Y₁ i)} {ν₂ : ∀ j, X₂ j → ProbDist (Y₂ j)}
    (hf : f.Memoryless ν₁) (hg : g.Memoryless ν₂) :
    (ProbStep.parallel f g).Memoryless (parallelLaw ν₁ ν₂) := by
  --        ┌───┐                  A query goes to one side only: that side answers, the other
  --   ────►│ f │  (state a)       keeps its state. So the reply law is the law of the side
  --        ├───┤                  that was queried.
  --   ────►│ g │  (state b)
  --        └───┘
  rintro ⟨a, b⟩ (i | j) x
  · -- a query at a left port `i`: the reply is `f`'s reply, of law `ν₁ i x`
    simp only [ProbStep.parallel, fTransform_fTransform]
    exact hf a i x
  · -- a query at a right port `j`: the reply is `g`'s reply, of law `ν₂ j x`
    simp only [ProbStep.parallel, fTransform_fTransform]
    exact hg b j x

end ProbStep

/-- **A probabilistic automaton with a memoryless step is the memoryless system** of its reply
law. -/
lemma RandomSystem.ofProbAutomaton_eq_memoryless {S I : Type} {X Y : I → Type}
    [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] (D : Domain (Σ i, X i) (Σ i, Y i))
    {step : ProbStep S I X Y} {ν : ∀ i, X i → ProbDist (Y i)} (hν : step.Memoryless ν)
    (init : ProbDist S) :
    RandomSystem.ofProbAutomaton D step init = RandomSystem.memoryless D (portLaw ν) := by
  -- Two random systems are equal when they give every transcript `t` the same probability.
  ext t
  -- Induct on `t`, adding one exchange `e = (x, y)` at the end:
  --
  --   automaton:   P(t · e) = Σ_s belief_t(s) · Pr[step s x replies y]   (forward algorithm)
  --                         = (Σ_s belief_t(s)) · ν x y                   (memoryless step)
  --                         = P(t) · ν x y
  --   memoryless:  P(t · e) = P(t) · ν x y                                (chain rule)
  induction t using List.reverseRecOn with
  | nil =>
    -- the empty transcript has probability 1 on both sides
    rw [mass_nil, mass_nil]
  | append_singleton t e ih =>
    -- automaton side: the probability of `t · e` is the weight of the forward belief after it
    rw [ofProbAutomaton_apply, ProbStep.belief_snoc]
    -- memoryless side: the chain rule, then the induction hypothesis for `t`
    rw [memoryless_snoc, ← ih]
    split_ifs
    · -- the domain admits the query `x`
      -- weight of the new belief = Σ over states of (old belief) × (probability of replying y)
      rw [ProbStep.weight_transition]
      -- the old weight is the probability of `t`, and the sum factors out the reply probability
      rw [ofProbAutomaton_apply, weight, Finsupp.sum_mul]
      -- every state replies `y` with the same probability (the step is memoryless)
      simp only [hν.mass_outcome]
    · -- the domain does not admit `x`: probability 0 on both sides
      rfl

namespace Program

variable {S O J R : Type} {U V : O → Type} {X Y : J → Type} (P : Program S O J U V X Y)

/-- **The reply law of an invocation** against inside replies of the laws `ν`: the body runs
from the exchanges `h`, with at most `n` more inside queries, and each inside query `q` is
answered by a fresh sample of `ν q`. -/
noncomputable def replyLaw (ν : ∀ j, X j → ProbDist (Y j)) (s : S) (o : O) (u : U o) :
    ℕ → List ((Σ j, X j) × (Σ j, Y j)) → Distribution (V o)
  -- No inside query is left: the body must reply now (otherwise no mass).
  | 0, h => match P s o u h with
    | .inl a => Finsupp.single a.2 1
    | .inr _ => 0
  -- The body replies (a point law on its reply), or asks `q` and continues with `y ← ν q`.
  | n + 1, h => match P s o u h with
    | .inl a => Finsupp.single a.2 1
    | .inr q => bindK (ν q.1 q.2).1 fun y => replyLaw ν s o u n (h ++ [(q, ⟨q.1, y⟩)])

variable {P}

/-- When the body replies, the reply law is the point law on its reply. -/
lemma replyLaw_inl {ν : ∀ j, X j → ProbDist (Y j)} {s : S} {o : O} {u : U o}
    {h : List ((Σ j, X j) × (Σ j, Y j))} {a : S × V o} (ha : P s o u h = .inl a) (n : ℕ) :
    P.replyLaw ν s o u n h = Finsupp.single a.2 1 := by
  cases n <;> simp [replyLaw, ha]

/-- When the body asks `q`, the reply law samples the answer `y ← ν q` and continues. -/
lemma replyLaw_succ_inr {ν : ∀ j, X j → ProbDist (Y j)} {s : S} {o : O} {u : U o}
    {h : List ((Σ j, X j) × (Σ j, Y j))} {q : Σ j, X j} (hq : P s o u h = .inr q) (n : ℕ) :
    P.replyLaw ν s o u (n + 1) h =
      bindK (ν q.1 q.2).1 fun y => P.replyLaw ν s o u n (h ++ [(q, ⟨q.1, y⟩)]) := by
  simp [replyLaw, hq]

/-- **An invocation against a memoryless step** replies with the reply law of the program,
whatever the state of the step. -/
lemma fTransform_snd_probInvoke {stepR : ProbStep R J X Y} {ν : ∀ j, X j → ProbDist (Y j)}
    (hν : stepR.Memoryless ν) (s : S) (o : O) (u : U o) :
    ∀ n r h, fTransform Prod.snd (P.probInvoke stepR s o u n r h) = P.replyLaw ν s o u n h := by
  -- `probInvoke` runs the body against the step, tracking (next state of the step, reply).
  -- Looking only at the reply, the state drops out: each inside answer has law `ν q`.
  -- Induction on the number `n` of inside queries still allowed.
  intro n
  induction n with
  | zero =>
    intro r h
    cases hq : P s o u h with
    | inl a =>
      -- the body replies `a.2`: a point law on both sides
      simp [probInvoke_inl hq, replyLaw_inl hq, fTransform]
    | inr q =>
      -- the body asks, but no query is left: no mass on both sides
      simp [probInvoke_zero_inr hq, replyLaw, hq, fTransform]
  | succ n ih =>
    intro r h
    cases hq : P s o u h with
    | inl a =>
      -- the body replies `a.2`: a point law on both sides
      simp [probInvoke_inl hq, replyLaw_inl hq, fTransform]
    | inr q =>
      -- the body asks `q`: the invocation samples the step's (next state, answer) and continues
      rw [probInvoke_succ_inr hq, replyLaw_succ_inr hq]
      -- move the projection to the reply inside the sampling
      rw [fTransform_bindK]
      -- the step's answer law, with the state forgotten, is `ν q` (memoryless)
      rw [← hν r q.1 q.2, bindK_fTransform]
      -- the continuation's reply law does not depend on the next state (induction hypothesis)
      simp only [ih, ProbStep.outcome, bindK_fTransform]
      rfl

/-- **A program against a memoryless step is memoryless**, when its reply law against `ν` is
the same `κ` in every state of the program. -/
lemma memoryless_probCombine {stepR : ProbStep R J X Y} {ν : ∀ j, X j → ProbDist (Y j)}
    (hν : stepR.Memoryless ν) {b : ℕ} (hb : P.Bounded b) {κ : ∀ o, U o → ProbDist (V o)}
    (hκ : ∀ s o u, P.replyLaw ν s o u b [] = (κ o u).1) :
    (P.probCombine stepR hb).Memoryless κ := by
  -- The combined step runs one invocation from the pair of states `(s, r)`.
  intro sr o u
  -- Its reply law is the program's reply law against `ν` from `s` (previous theorem) ...
  have reply := fTransform_snd_probInvoke (P := P) hν sr.1 o u b sr.2 []
  -- ... which is `κ o u` by hypothesis.
  exact reply.trans (hκ sr.1 o u)

end Program

/-! ## Typed systems and converters

A typed system is its random system (`.1`) with the proof that it replies at the queried port;
two typed systems are equal when their random systems are. The laws below compute the random
system of a typed system built from programs and memoryless parts. -/

/-- **A system presented as memoryless fresh sampling is the memoryless system.** -/
lemma FreshSampling.memoryless_eq {B : Interface} {R : Interface.Resource B}
    (Φ : FreshSampling B R) {ν : ∀ j, B.X j → ProbDist (B.Y j)} (hν : Φ.stepF.Memoryless ν) :
    R.1 = RandomSystem.memoryless B.inputDomain (RandomSystem.portLaw ν) := by
  -- the system is the probabilistic automaton of its fresh-sampling step
  rw [Φ.eq_fresh]
  -- that automaton has a memoryless step, so it is the memoryless system
  exact RandomSystem.ofProbAutomaton_eq_memoryless _ hν _

namespace Interface.Converter

variable {A B : Interface} {S : Type} {R : Resource B} {ν : ∀ j, B.X j → ProbDist (B.Y j)}
  {κ : ∀ o, A.X o → ProbDist (A.Y o)}

/-- **The composition law** for a program: on a system presented as memoryless fresh sampling
of `ν`, the converter of a program with the reply law `κ` against `ν` gives the memoryless
system of `κ`. -/
lemma ofProgram_smul_memoryless (Φ : FreshSampling B R) (hν : Φ.stepF.Memoryless ν) (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    (hB : ∀ xs, xs ≠ [] → xs.length ≤ b * A.bound → B.domain xs)
    (hκ : ∀ s o u, P.replyLaw ν s o u b [] = (κ o u).1) :
    (ofProgram s P hb hB • R).1 =
      RandomSystem.memoryless A.inputDomain (RandomSystem.portLaw κ) := by
  -- the attached converter is presented as fresh sampling: the program run against `R`'s step
  let Ψ := Φ.ofProgram s P hb hB
  -- that step is memoryless with the reply law `κ`
  have hstep : Ψ.stepF.Memoryless κ := Program.memoryless_probCombine hν hb hκ
  exact Ψ.memoryless_eq hstep

/-- **The composition law** for a port-preserving program. -/
lemma ofPreservingProgram_smul_memoryless (Φ : FreshSampling B R) (hν : Φ.stepF.Memoryless ν)
    (s : S) (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    (ι : A.I → Option B.I) (hι : P.PortPreserving ι) (q : A.I → ℕ)
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) → B.domain ys)
    (hκ : ∀ s o u, P.replyLaw ν s o u b [] = (κ o u).1) :
    (ofPreservingProgram s P hb ι hι q hA hB • R).1 =
      RandomSystem.memoryless A.inputDomain (RandomSystem.portLaw κ) := by
  -- as for `ofProgram`: only the budgets of the converter differ
  let Ψ := Φ.ofPreservingProgram s P hb ι hι q hA hB
  have hstep : Ψ.stepF.Memoryless κ := Program.memoryless_probCombine hν hb hκ
  exact Ψ.memoryless_eq hstep

open CategoryTheory in
/-- **The composition law** for a port-preserving program with a source beside its inside
interface: its local samples are fresh samples of the source's law.

```
        ┌───┐ ──── inside ────────► R, memoryless with ν
  ─────►│ 𝓡 │
        └───┘ ──── randomness ────► source, fresh samples of law
```
-/
lemma ofPreservingProgram_comp_rightContext_smul_memoryless (Φ : FreshSampling B R)
    (hν : Φ.stepF.Memoryless ν) {Z : Type} [Fintype Z] (law : ProbDist Z) (n : ℕ) (s : S)
    (P : Program S A.I (Interface.tensor B (Interface.source Z n)).I A.X A.Y
      (Interface.tensor B (Interface.source Z n)).X (Interface.tensor B (Interface.source Z n)).Y)
    {b : ℕ} (hb : P.Bounded b) (ι : A.I → Option (Interface.tensor B (Interface.source Z n)).I)
    (hι : P.PortPreserving ι) (q : A.I → ℕ)
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) →
        (Interface.tensor B (Interface.source Z n)).domain ys)
    (hκ : ∀ s o u, P.replyLaw (ProbStep.parallelLaw ν fun _ _ => law) s o u b [] = (κ o u).1) :
    ((ofPreservingProgram s P hb ι hι q hA hB ≫ Interface.rightContext B (Resource.source law n)) •
      R).1 = RandomSystem.memoryless A.inputDomain (RandomSystem.portLaw κ) := by
  -- Step 1: the source of `law` is fresh sampling, with a memoryless step of law `law`.
  let Φsource := FreshSampling.source law n
  have hsource : Φsource.stepF.Memoryless fun _ _ => law := ProbStep.memoryless_fresh law
  -- Step 2: `R` and the source side by side are fresh sampling, memoryless with the law of the
  -- side that is queried.
  let Φboth := Φ.parallel Φsource
  have hboth : Φboth.stepF.Memoryless (ProbStep.parallelLaw ν fun _ _ => law) :=
    hν.parallel hsource
  -- Step 3: the program attached to both: fresh sampling again, the program run against the
  -- side-by-side step; composing with `rightContext` places the source beside `R`.
  let Ψ := FreshSampling.ofRightContext _ (Φboth.ofPreservingProgram s P hb ι hι q hA hB)
  -- Step 4: a program against a memoryless step is memoryless, with its reply law `κ`.
  have hstep : Ψ.stepF.Memoryless κ := Program.memoryless_probCombine hboth hb hκ
  exact Ψ.memoryless_eq hstep

end Interface.Converter

end SystemAlgebra

/-! ## The DSL memoryless source -/

namespace Commons

open Probability Probability.Distribution SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface
open scoped SystemAlgebra SystemAlgebra.DSL

-- The memoryless source of `ν` [1, Definition 3.1]: on `eval(())`, `y ←$ ν`, return `y`.
system MemorylessSource(Y : Type) [Fintype Y] (ν : Distribution.ProbDist Y) : Evaluation Unit Y
  on eval(_input : Unit) → Y
    y ←$ ν
    return y

noncomputable section

variable {Y : Type} [Fintype Y] (ν : ProbDist Y) (q : Evaluation.Port → ℕ)

/-- The memoryless source as fresh sampling: its program run against its table of samples. -/
def MemorylessSource.freshSampling :
    FreshSampling (Evaluation.perPort Unit Y q) (MemorylessSource.perPort Y ν (budget := q)) :=
  (FreshSampling.source (MemorylessSource.law1 Y ν) _).ofProgram none _ _ _

/-- Its fresh-sampling step replies with the law `ν`. -/
lemma MemorylessSource.step_memoryless :
    (MemorylessSource.freshSampling ν q).stepF.Memoryless fun _ _ => ν := by
  -- The step is the program run against the fresh samples of its source; the program is
  -- memoryless once we know the law of one invocation.
  refine Program.memoryless_probCombine (ProbStep.memoryless_fresh _)
    (MemorylessSource.bound_spec Y ν) ?_
  -- One invocation:  eval(()) ──► draw y ← ν ──► reply y.  Its law is `ν`, in both
  -- initialization states (`none` before the first call, `some ()` after).
  rintro (_ | ⟨⟩) ⟨⟩ ⟨⟩
  · simp [Program.replyLaw, MemorylessSource.body, MemorylessSource.law1, callProg, returnProg,
      bindK_single_one]
  · simp [Program.replyLaw, MemorylessSource.body, MemorylessSource.law1, callProg, returnProg,
      bindK_single_one]

/-- **The DSL source of `ν` is the memoryless system of `ν`.** -/
lemma MemorylessSource.memoryless_eq :
    (MemorylessSource.perPort Y ν (budget := q)).1 =
      RandomSystem.memoryless _ (RandomSystem.portLaw fun _ _ => ν) :=
  (MemorylessSource.freshSampling ν q).memoryless_eq (MemorylessSource.step_memoryless ν q)

end

end Commons
