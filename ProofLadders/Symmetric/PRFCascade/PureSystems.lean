import ProofLadders.Symmetric.PRFCascade.Basic
import ProofLadders.Common.Symmetric
import ProofLadders.Common.Functional
import ProofLadders.Common.Programs
import ProofLadders.Common.HCoefficient

/-!
# PRF cascade: pure systems

Statements about random functions alone, for the cascade of [1, §2]: information-theoretic, with
no PRF step and no DSL system or converter. The cascade with ideal components is the converter
`π`, which queries its first component and then its second at the reply: the converter of the
deterministic program `π.body`, a function of its inside exchanges, typed at per-label budgets,
`q` queries making at most `q` to each component. On two independent uniform random functions it
is the composition `T₂ ∘ T₁` (`π_smul_urf`), within `q(q-1)/(2|X|)` of the uniform random function
(`cascade_construction`). The distance is the probability of a collision under `T₁`, bounded by
two techniques:

* conditional equivalence [2, §4.11] (`composedURF_distance_le`): `T₂ ∘ T₁` with a monotone
  binary output that records a collision under `T₁` is conditionally equivalent to the uniform
  random function (`cascade_game_equiv`), so the distance is at most the probability of a
  collision on fixed inputs (`cascadeGame_blind_bound`) [2, Theorem 4.17];
* the H-coefficient technique (`composedURF_distance_le_hCoefficient`), without bad transcripts:
  at a transcript with `d` distinct inputs, the uniform random function has probability
  `|X|^{-d}`, and `T₂ ∘ T₁` at least `(1 - q(q-1)/(2|X|)) |X|^{-d}` (`composedURF_ratio`).

The collision step of the bonus `k₁ = k₂` is the same argument for the self-composition `T ∘ T`
of one uniform random function, within `q(3q-1)/(2|X|)` by conditional equivalence
(`selfComposedURF_distance_le`).

```
            ┌───┐ ── first.eval(x)  ⇒ T₁(x) ──► ┌───────────────┐
   eval(x)  │ π │                               │ T₁ ← (X → X)  │  URF
   ───────► │   │                               └───────────────┘
   ◄─────── │   │ ── second.eval(y) ⇒ T₂(y) ──► ┌───────────────┐
   T₂(T₁ x) └───┘                               │ T₂ ← (X → X)  │  URF
                                                └───────────────┘
```

## Main definitions

* `Collision T₁ xs`: two queried inputs collide under `T₁`
* `SelfCollision T xs`: two queried inputs collide under `T`, or a value `T(x)` is a queried input
* `π.body X`, `π.perLabel X q`: the program of the cascade with ideal components, and its
  converter at per-label budgets
* `cascadeGame X q`: the collision game of `T₂ ∘ T₁`
* `selfComposedURF X`, `sameKeyGame X q`: the self-composition `T ∘ T`, and its collision game

## Main results

* `π_smul_urf`, `cascade_construction`: the cascade with ideal components is `T₂ ∘ T₁`, within
  `q(q-1)/(2|X|)` of the uniform random function
* `cascade_game_equiv`, `cascadeGame_blind_bound`, `composedURF_distance_le`: the bound by
  conditional equivalence
* `collision_mass_le`, `composition_values_mass_ge`, `composedURF_ratio`,
  `composedURF_distance_le_hCoefficient`: the bound by the H-coefficient technique
* `sameKeyGame_equiv`, `sameKeyGame_blind_bound`, `selfComposedURF_distance_le`: `T ∘ T`

## References

1. The symmetric proof ladder, *Security proofs in the style of The Joy of Cryptography*,
   `proof-ladders/symmetric-ladder`, `Notes/selfcontained.tex`.
2. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

namespace ProofLadders.PRFCascade.PureSystems

open Commons Probability SystemAlgebra SystemAlgebra.Interface
open scoped SystemAlgebra

/-! ### Collisions -/

section

variable {X : Type}

/-- Two distinct queried inputs collide under `T₁`. -/
def Collision (T₁ : X → X) (xs : List X) : Prop :=
  ∃ x ∈ xs, ∃ x' ∈ xs, x ≠ x' ∧ T₁ x = T₁ x'

/-- A collision stays a collision when more inputs are queried. -/
lemma collision_monotone (T₁ : X → X) {xs xs' : List X} (hp : xs <+: xs') :
    Collision T₁ xs → Collision T₁ xs' :=
  -- The two colliding inputs are still among the inputs of the extended list.
  fun ⟨x, hx, x', hx', distinct, equal⟩ =>
    ⟨x, hp.subset hx, x', hp.subset hx', distinct, equal⟩

/-- The first-level values `T(x)` of the queried inputs collide, or one of them is a queried
input. -/
def SelfCollision (T : X → X) (xs : List X) : Prop :=
  Collision T xs ∨ ∃ x ∈ xs, T x ∈ xs

/-- A self-collision stays one when more inputs are queried. -/
lemma selfCollision_monotone (T : X → X) {xs xs' : List X} (hp : xs <+: xs') :
    SelfCollision T xs → SelfCollision T xs'
  -- A collision stays a collision, ...
  | .inl collision => .inl (collision_monotone T hp collision)
  -- ... and a first-level value that is a queried input stays one.
  | .inr ⟨x, hx, hTx⟩ => .inr ⟨x, hp.subset hx, hp.subset hTx⟩

end

noncomputable section

/-! ### The cascade with ideal components -/

section Construction

variable {X : Type} [Fintype X]

variable (X) in
/-- **The program of `π`**, the cascade with ideal components, on the inside interface of two
components side by side, `first` on the left and `second` on the right: an invocation on `x`
queries `first.eval(x) ⇒ y`, then `second.eval(y) ⇒ z`, and replies `z`. It keeps no state. -/
def π.body : Program Unit Evaluation.Port (Evaluation.Port ⊕ Evaluation.Port)
    (Evaluation.Input X) (Evaluation.Output X)
    (Sum.rec (Evaluation.Input X) (Evaluation.Input X))
    (Sum.rec (Evaluation.Output X) (Evaluation.Output X))
  -- No exchange yet: query `first.eval(x)`.
  | _, .eval, x, [] => .inr ⟨.inl .eval, x⟩
  -- After `first.eval(x) ⇒ y`: query `second.eval(y)`.
  | _, .eval, _, [(_, ⟨.inl .eval, y⟩)] => .inr ⟨.inr .eval, y⟩
  -- After `second.eval(y) ⇒ z`: reply `z`.
  | s, .eval, _, [_, (_, ⟨.inr .eval, z⟩)] => .inl (s, z)
  -- Exchanges the body does not make itself: query `first.eval(x)`.
  | _, .eval, x, _ => .inr ⟨.inl .eval, x⟩

/-- **The queries of `π`**: along the exchanges it makes itself, an invocation on `x` queries
`first.eval(x)` before any exchange and `second.eval(y)` after `first.eval(x) ⇒ y`, and no other
query. -/
lemma π.body_query {s : Unit} {o : Evaluation.Port} {x : Evaluation.Input X o}
    {h : List ((Σ j, Sum.rec (Evaluation.Input X) (Evaluation.Input X) j) ×
      (Σ j, Sum.rec (Evaluation.Output X) (Evaluation.Output X) j))}
    {q : Σ j, Sum.rec (Evaluation.Input X) (Evaluation.Input X) j}
    (hc : Program.ExchangesOf (π.body X s o x) h) (hq : π.body X s o x h = .inr q) :
    (h = [] ∧ q = ⟨.inl .eval, x⟩) ∨
      ∃ y : X, h = [(⟨.inl .eval, x⟩, ⟨.inl .eval, y⟩)] ∧ q = ⟨.inr .eval, y⟩ := by
  -- The one outside port.
  cases o
  -- No exchange, one, or at least two.
  rcases h with _ | ⟨⟨⟨j₁, x₁⟩, ⟨j₁', y⟩⟩, _ | ⟨⟨⟨j₂, x₂⟩, ⟨j₂', z⟩⟩, h⟩⟩
  · -- No exchange: the query is `first.eval(x)`.
    simp [π.body] at hq
    exact .inl ⟨rfl, hq.symm⟩
  · -- One exchange: the body made it, so it is `first.eval(x) ⇒ y`, ...
    obtain ⟨h₁, h₁'⟩ := hc 0 (by simp)
    simp [π.body] at h₁ h₁'
    obtain ⟨rfl, rfl⟩ := h₁
    subst h₁'
    -- ... and the query is `second.eval(y)`.
    simp [π.body] at hq
    exact .inr ⟨y, rfl, hq.symm⟩
  · -- Two exchanges or more: the first is `first.eval(x) ⇒ y`, ...
    obtain ⟨h₁, h₁'⟩ := hc 0 (by simp)
    simp [π.body] at h₁ h₁'
    obtain ⟨rfl, rfl⟩ := h₁
    subst h₁'
    -- ... the second `second.eval(y) ⇒ z`, ...
    obtain ⟨h₂, h₂'⟩ := hc 1 (by simp)
    simp [π.body] at h₂ h₂'
    obtain ⟨rfl, rfl⟩ := h₂
    subst h₂'
    -- ... and after them the body replies: it makes no query, and no third exchange.
    rcases h with _ | ⟨e, h⟩
    · simp [π.body] at hq
    · obtain ⟨h₃, -⟩ := hc 2 (by simp)
      simp [π.body] at h₃

variable (X) in
/-- `π` makes at most two inside queries per invocation. -/
lemma π.bounded : (π.body X).Bounded 2 := by
  intro s o x h q hc hq
  -- A query comes after no exchange or after one.
  rcases π.body_query hc hq with ⟨rfl, -⟩ | ⟨y, rfl, -⟩ <;> simp

/-- The inside calls of `π` per query: one to each component. -/
def π.calls : Evaluation.Port → Evaluation.Port ⊕ Evaluation.Port → ℕ := fun _ _ => 1

/-- `π` calls each component at most once per query. -/
lemma π.labelBounded : (π.body X).LabelBounded π.calls := by
  intro s o x h q hc hq
  rcases π.body_query hc hq with ⟨rfl, -⟩ | ⟨y, rfl, rfl⟩
  · -- `first.eval(x)`, before any exchange: no earlier query to `first`.
    simp [π.calls]
  · -- `second.eval(y)`, after the exchange with `first`: no earlier query to `second`.
    simp [π.calls, SystemAlgebra.restrict]

/-- `q` queries to `π` make at most `q` queries to each component. -/
lemma π.admits (q : Evaluation.Port → ℕ) :
    ((Queries X q).tensor (Queries X q)).AdmitsLabelBudget fun j => ∑ o, π.calls o j * q o := by
  -- The two components side by side admit `q` queries each, which is `∑ o, 1 · q o`.
  refine (portBudget_tensor_admitsLabelBudget _ _ _ _ _ _ q q).mono fun j => ?_
  rcases j with ⟨⟩ | ⟨⟩ <;> simp [π.calls]

variable (X) in
/-- **`π` at per-port budgets**: `q` queries, and `q` to each component; the converter of its
program, started in the trivial state. -/
def π.perLabel (q : Evaluation.Port → ℕ) : Queries X q ⟶ (Queries X q).tensor (Queries X q) :=
  Converter.ofLabelBoundedProgram (A := Queries X q) (B := (Queries X q).tensor (Queries X q))
    () (π.body X) (π.bounded X) π.calls π.labelBounded q (fun _ hd => hd.2) (π.admits q)

variable [DecidableEq X] [Nonempty X]

variable (X) in
/-- **The cascade with ideal components is `T₂ ∘ T₁`**: `π` on two independent uniform random
functions is the composition of two independent uniform functions. -/
lemma π_smul_urf (q : Evaluation.Port → ℕ) :
    π.perLabel X q • (URF (Queries X q) ∥ URF (Queries X q)) = composedURF X := by
  --            ┌───┐ ── first.eval(x)  ⇒ T₁(x) ──► ┌───────────────┐
  --   eval(x)  │ π │                               │ T₁ ← (X → X)  │  URF
  --   ───────► │   │                               └───────────────┘
  --   ◄─────── │   │ ── second.eval(y) ⇒ T₂(y) ──► ┌───────────────┐
  --   T₂(T₁ x) └───┘                               │ T₂ ← (X → X)  │  URF
  --                                                └───────────────┘
  --
  -- Each uniform random function is the automaton holding a uniform function, and side by side
  -- they are the automaton holding the pair `(T₁, T₂)`, of the product law.
  rw [URF_perPort_eq_ofAutomaton, parallel_ofAutomaton]
  -- `π` is its program; attached to the automaton, it is the combined automaton.
  unfold π.perLabel Converter.ofLabelBoundedProgram
  rw [Interface.ofDDC_ofProgramOn_smul_ofAutomaton (A := Queries X q)
    (B := (Queries X q).tensor (Queries X q)) () (π.body X) (π.bounded X)]
  -- One invocation on `x`: `first.eval(x) ⇒ T₁(x)`, `second.eval(T₁ x) ⇒ T₂(T₁ x)`; the pair of
  -- functions is kept.
  have step : ∀ (T : (X → X) × (X → X)) (x : X),
      (π.body X).combine (parallelStep (fun (f : X → X) _ x => (f, f x))
        (fun (f : X → X) _ x => (f, f x))) (π.bounded X) ((), T) .eval x =
        (((), T), T.2 (T.1 x)) := fun T x =>
    Program.combine_eq_of_invoke _ _ (n := 2) (by
      simp [Program.invoke, π.body, parallelStep])
  -- So the combined automaton started on `(T₁, T₂)` is the function `T₂ ∘ T₁`, and the
  -- automaton with a sampled pair is the sampled function.
  refine (Resource.ofAutomaton_eq_sample _ (Distribution.prod (Distribution.uniform (X → X))
    (Distribution.uniform (X → X))) (fun T => ((), T)) (fun T _ x => T.2 (T.1 x))
    fun T => ?_).trans ?_
  · -- A bisimulation with the one-state automaton of `T₂ ∘ T₁`: the pair stays `T`.
    rw [functionSystem_eq_automatonSystem]
    refine automatonSystem_eq_of_bisim _ (rel := fun s (_ : Unit) => s.2 = T) ?_ rfl
    rintro ⟨⟨⟩, T'⟩ ⟨⟩ ⟨⟩ x rfl
    rw [step]
    exact ⟨rfl, rfl⟩
  · -- The product of two uniform laws is the uniform law on pairs.
    rw [composedURF]
    exact Resource.sample_congr_law Distribution.prod_uniform _

end Construction

variable (X : Type) [Fintype X] [DecidableEq X] [Nonempty X]

/-! ### The bound by conditional equivalence -/

/-- **The collision game** of `T₂ ∘ T₁`: the sampled pair of functions, with the hidden condition
that two queried inputs collide under `T₁`. -/
def cascadeGame (q : Evaluation.Port → ℕ) :=
  PDG.ofSingleFunction (Queries X q).domain (Queries X q).nonempty_prefix
    (Queries X q).bound (Queries X q).length_le
    (Distribution.uniform ((X → X) × (X → X))) (fun T x => T.2 (T.1 x))
    (fun T => ⟨Collision T.1, fun {_ _} hp => collision_monotone T.1 hp⟩)

/-- Without a collision under `T₁`, the transcripts of `T₂ ∘ T₁` have the law of the uniform
random function. -/
lemma cascade_game_equiv (q : Evaluation.Port → ℕ) :
    cascadeGame X q |≡ URF (Queries X q) := by
  classical
  -- The uniform random function samples a uniform function once.
  rw [URF_perPort_eq]
  -- It suffices to factor, at fixed inputs `xs` and prescribed values `answers`: the
  -- probability of these values and no collision is the probability of the values under a
  -- uniform function times the probability of no collision.
  apply PDG.ofSingleFunction_gameEquivalent
  intro xs answers
  -- A uniform function takes the values at the `d` distinct inputs with probability `|X|^{-d}`.
  have ideal := Counting.uniform_mass_apply_list_eq (Y := X) xs id (Set.injOn_id _) answers
  simp only [id] at ideal
  -- (Unfolding the factorization goal at `xs` and `answers`.)
  dsimp only
  rw [ideal]
  -- The uniform pair is two independent uniform functions; no collision depends on `T₁` only,
  -- with `T₂` integrated out (weight `1`).
  rw [← Distribution.prod_uniform, Distribution.mass_prod_fst (R := fun T₁ => ¬ Collision T₁ xs),
    Distribution.weight_uniform, mul_one]
  -- The probability of the values and no collision is the average over `T₁` of its probability
  -- over `T₂`.
  refine (Distribution.mass_prod_eq_sum _ _ (fun (T₁ T₂ : X → X) =>
    (∀ x ∈ xs, T₂ (T₁ x) = answers x) ∧ ¬ Collision T₁ xs)).trans ?_
  -- Without a collision under `T₁`, the values of `T₂` at the distinct points `T₁(x)` are
  -- uniform and independent of `T₁`.
  have fresh : ∀ T₁ : X → X,
      (Distribution.uniform (X → X)).mass
        (fun T₂ => (∀ x ∈ xs, T₂ (T₁ x) = answers x) ∧ ¬ Collision T₁ xs) =
      if ¬ Collision T₁ xs then (1 / (Fintype.card X : ℝ)) ^ xs.toFinset.card else 0 := by
    intro T₁
    by_cases hc : Collision T₁ xs
    · -- A collision: the event is impossible.
      rw [if_neg (not_not.mpr hc)]
      exact Distribution.mass_eq_zero_of_forall_not _ fun _ h => h.2 hc
    · -- No collision: `T₁` is injective on the inputs, and `T₂` takes the values at `d` distinct
      -- points with probability `|X|^{-d}`.
      rw [if_pos hc, ← Counting.uniform_mass_apply_list_eq xs T₁ (fun x hx x' hx' h => by
        by_contra hne
        exact hc ⟨x, List.mem_toFinset.mp hx, x', List.mem_toFinset.mp hx', hne, h⟩) answers]
      exact Distribution.mass_congr _ fun T₂ => and_iff_left hc
  -- Averaged over `T₁`: `|X|^{-d}` times the probability of no collision.
  simp only [fresh, mul_ite, mul_zero]
  rw [Distribution.mass, Finsupp.mul_sum]
  exact Finsupp.sum_congr fun T₁ _ => by split_ifs <;> ring

/-- Blind winning is a collision under `T₁` among at most `q` fixed inputs. -/
lemma cascadeGame_blind_bound (q : Evaluation.Port → ℕ) :
    ν((cascadeGame X q).blind (Queries X q).nonempty_prefix) ≤
      (q .eval : ℝ) * ((q .eval : ℝ) - 1) / (2 * Fintype.card X) := by
  -- The bound `q(q-1)/(2|X|)` is non-negative.
  have hq : 0 ≤ (q .eval : ℝ) * ((q .eval : ℝ) - 1) := by
    simpa using natCast_mul_sub_one_le (Nat.zero_le (q .eval)) le_rfl
  -- A blind player fixes its inputs: it suffices to bound the probability of a collision at
  -- every admitted list of inputs.
  apply PDG.ofFunction_blind_le (div_nonneg hq (by positivity))
  intro xs hxs
  -- The distinct inputs: at most `q`.
  let S := (xs.map Sigma.snd).toFinset
  have hS : S.card ≤ q .eval :=
    (List.toFinset_card_le _).trans ((List.length_map _).trans_le (evaluation_length_le hxs))
  -- The blind winning event at these inputs: a collision under `T₁`.
  change (Distribution.uniform ((X → X) × (X → X))).mass
    (fun T => Collision T.1 (xs.map Sigma.snd)) ≤ _
  -- A collision depends on `T₁` only: integrate `T₂` out (weight `1`).
  rw [← Distribution.prod_uniform, Distribution.mass_prod_fst (R := fun T₁ =>
    Collision T₁ (xs.map Sigma.snd)), Distribution.weight_uniform, mul_one]
  calc _ = (Distribution.uniform (X → X)).mass
        (fun T₁ => ∃ x ∈ S, ∃ x' ∈ S, x ≠ x' ∧ T₁ x = T₁ x') :=
        -- A collision is a pair of distinct inputs with equal values.
        Distribution.mass_congr _ fun T₁ => by simp [Collision, S]
    _ ≤ S.card * (S.card - 1) / 2 * (1 / Fintype.card X) :=
        -- The union bound over the `d(d-1)/2` pairs; two distinct points of a uniform function
        -- agree with probability at most `1/|X|`.
        Distribution.mass_exists_pair_le Distribution.uniform_nonNeg S _
          (fun _ _ _ h => h.symm) fun _ _ _ _ h => Counting.uniform_mass_apply_eq_le h
    _ ≤ _ := by
        -- `d(d-1)/2 · 1/|X| = d(d-1)/(2|X|)`, at most `q(q-1)/(2|X|)` since `d ≤ q`.
        rw [div_mul_div_comm, mul_one]
        exact div_le_div_of_nonneg_right (by simpa using natCast_mul_sub_one_le hS le_rfl)
          (by positivity)

/-- **The collision step, by conditional equivalence**: `T₂ ∘ T₁` is within `q(q-1)/(2|X|)` of
the uniform random function. -/
theorem composedURF_distance_le (q : Evaluation.Port → ℕ) :
    Δ (composedURF X (q := q)) (URF (Queries X q)) ≤
      ENNReal.ofReal ((q .eval : ℝ) * ((q .eval : ℝ) - 1) / (2 * Fintype.card X)) :=
  -- The game is conditionally equivalent to the uniform random function and presents
  -- `composedURF` (`rfl`), so the distance is at most the game's blind winning probability
  -- [2, Theorem 4.17], which is the collision bound.
  ((cascade_game_equiv X q).game_dist_ofSingleFunction_le rfl).trans
    (ENNReal.ofReal_le_ofReal (cascadeGame_blind_bound X q))

/-- **The cascade construction with ideal components**: `π` on two independent uniform random
functions is within `q(q-1)/(2|X|)` of the uniform random function. -/
theorem cascade_construction (q : Evaluation.Port → ℕ) :
    Δ (π.perLabel X q • (URF (Queries X q) ∥ URF (Queries X q))) (URF (Queries X q)) ≤
      ENNReal.ofReal ((q .eval : ℝ) * ((q .eval : ℝ) - 1) / (2 * Fintype.card X)) := by
  -- `π • (URF ∥ URF)` is `T₂ ∘ T₁` ...
  rw [π_smul_urf]
  -- ... within the collision bound, by conditional equivalence.
  exact composedURF_distance_le X q

/-! ### The bound by the H-coefficient technique -/

variable {X} in
/-- **A collision under a uniform `T₁`** among inputs with at most `m` distinct values has
probability at most `m(m-1)/(2|X|)`: a union bound over the pairs of distinct inputs, each pair
colliding with probability `1/|X|`. -/
lemma collision_mass_le {xs : List X} {m : ℕ} (hm : xs.toFinset.card ≤ m) :
    (Distribution.uniform (X → X)).mass (fun T₁ => Collision T₁ xs) ≤
      (m : ℝ) * ((m : ℝ) - 1) / (2 * Fintype.card X) := by
  calc _ = (Distribution.uniform (X → X)).mass
        (fun T₁ => ∃ x ∈ xs.toFinset, ∃ x' ∈ xs.toFinset, x ≠ x' ∧ T₁ x = T₁ x') :=
        -- A collision is a pair of distinct values among the inputs, equal under `T₁`.
        Distribution.mass_congr _ fun T₁ => by simp [Collision]
    _ ≤ xs.toFinset.card * (xs.toFinset.card - 1) / 2 * (1 / Fintype.card X) :=
        -- The union bound over the `d(d-1)/2` pairs of the `d` distinct inputs: the event is
        -- symmetric in the pair, and two distinct points of a uniform function agree with
        -- probability at most `1/|X|`.
        Distribution.mass_exists_pair_le Distribution.uniform_nonNeg _ _
          (fun _ _ _ equal => equal.symm) fun _ _ _ _ distinct =>
            Counting.uniform_mass_apply_eq_le distinct
    _ ≤ _ := by
        -- `d(d-1)/2 · 1/|X|` is `d(d-1)/(2|X|)`, ...
        rw [div_mul_div_comm, mul_one]
        -- ... at most `m(m-1)/(2|X|)`, since `d ≤ m`.
        exact div_le_div_of_nonneg_right (by simpa using natCast_mul_sub_one_le hm le_rfl)
          (by positivity)

variable {X} in
/-- **`T₂ ∘ T₁` takes prescribed values** `a` at the inputs `xs`, with `d` distinct values, with
probability at least that of no collision under `T₁` times `|X|^{-d}`: without a collision,
`T₂` is evaluated at `d` distinct points. -/
lemma composition_values_mass_ge (xs : List X) (a : X → X) :
    (Distribution.uniform (X → X)).mass (fun T₁ => ¬ Collision T₁ xs) *
        (1 / (Fintype.card X : ℝ)) ^ xs.toFinset.card ≤
      (Distribution.uniform ((X → X) × (X → X))).mass
        (fun T => ∀ x ∈ xs, T.2 (T.1 x) = a x) := by
  classical
  --        x       x'      x''        the d distinct inputs
  --        │T₁     │T₁     │T₁
  --        ▼       ▼       ▼
  --       T₁x  ≠  T₁x'  ≠  T₁x''      no collision: d distinct points
  --        │T₂     │T₂     │T₂
  --        ▼       ▼       ▼
  --       a x     a x'    a x''       each with probability 1/|X|, independently
  --
  -- For a fixed `T₁`, the probability over `T₂` of no collision and the values `a`.
  have fresh : ∀ T₁ : X → X, (Distribution.uniform (X → X)).mass
      (fun T₂ => ¬ Collision T₁ xs ∧ ∀ x ∈ xs, T₂ (T₁ x) = a x) =
      if ¬ Collision T₁ xs then (1 / (Fintype.card X : ℝ)) ^ xs.toFinset.card else 0 := by
    intro T₁
    by_cases collision : Collision T₁ xs
    · -- A collision: the event is impossible.
      rw [if_neg (not_not.mpr collision)]
      exact Distribution.mass_eq_zero_of_forall_not _ fun _ event => event.1 collision
    · -- No collision: `T₁` is injective on the distinct inputs, ...
      have injective : Set.InjOn T₁ xs.toFinset := fun x hx x' hx' equal => by
        by_contra distinct
        exact collision
          ⟨x, List.mem_toFinset.mp hx, x', List.mem_toFinset.mp hx', distinct, equal⟩
      -- ... so `T₂` takes the values `a` at the `d` distinct points `T₁ x` with probability
      -- `|X|^{-d}`.
      rw [if_pos collision, ← Counting.uniform_mass_apply_list_eq xs T₁ injective a]
      exact Distribution.mass_congr _ fun T₂ => and_iff_right collision
  calc _ = (Distribution.uniform ((X → X) × (X → X))).mass
        (fun T => ¬ Collision T.1 xs ∧ ∀ x ∈ xs, T.2 (T.1 x) = a x) := by
        -- A uniform pair is a pair of independent uniform functions, ...
        rw [← Distribution.prod_uniform]
        -- ... so the probability of the event is the average over `T₁` of its probability
        -- over `T₂`, ...
        refine Eq.trans ?_ (Distribution.mass_prod_eq_sum _ _
          (fun T₁ T₂ : X → X => ¬ Collision T₁ xs ∧ ∀ x ∈ xs, T₂ (T₁ x) = a x)).symm
        -- ... which is `|X|^{-d}` without a collision and `0` with one; ...
        simp only [fresh]
        -- ... averaged over `T₁`, the probability of no collision times `|X|^{-d}`.
        unfold Distribution.mass
        rw [Finsupp.sum_mul]
        exact Finsupp.sum_congr fun T₁ _ => by split_ifs <;> ring
    _ ≤ _ :=
        -- Dropping the condition of no collision.
        Distribution.mass_mono Distribution.uniform_nonNeg fun _ event => event.2

/-- **The ratio of the collision step**: on every transcript `h`, the random system of
`T₂ ∘ T₁` is at least `1 - q(q-1)/(2|X|)` times that of the uniform random function. -/
lemma composedURF_ratio (q : Evaluation.Port → ℕ)
    (h : List ((Σ i, (Queries X q).X i) × (Σ i, (Queries X q).Y i))) :
    (1 - (q .eval : ℝ) * ((q .eval : ℝ) - 1) / (2 * Fintype.card X)) *
        (URF (Queries X q)).1 h ≤ (composedURF X (q := q)).1 h := by
  classical
  --          x                                    x
  --    D ─────────► ┌─────────────────┐     D ─────────► ┌─────────────┐
  --      ◄───────── │ T₁, T₂ ← X → X  │       ◄───────── │ g ← X → X   │
  --       T₂(T₁ x)  └─────────────────┘          g(x)    └─────────────┘
  --                    composedURF X                      URF (Queries X q)
  --
  --    h  = (x₁, y₁) (x₂, y₂) … (x_m, y_m)    queries xᵢ, replies yᵢ
  --    xs = x₁ x₂ … x_m                        d distinct values
  --
  -- A function `f` answers `h` when `h` is admitted (at most `q` queries, so `m ≤ q`) and
  -- `yᵢ = f(xᵢ)` for every `i`. A sampled function gives `h` the probability that it answers
  -- `h` (`Resource.sample_ofFunction_apply`).
  -- The ideal system: the probability that a uniform `g` answers `h`.
  rw [URF_perPort_eq, Resource.sample_ofFunction_apply]
  -- The real system: the probability that `T₂ ∘ T₁` answers `h`, for a uniform pair.
  have real : (composedURF X (q := q)).1 h =
      (Distribution.uniform ((X → X) × (X → X))).mass (fun T =>
        (h = [] ∨ (Queries X q).domain (h.map Prod.fst)) ∧
          ∀ z ∈ h, z.2 = ⟨z.1.1, T.2 (T.1 z.1.2)⟩) := by
    -- `composedURF X` samples the pair `T` and answers with the function `T₂ ∘ T₁`.
    unfold composedURF
    rw [Resource.sample_ofFunction_apply]
  rw [real]
  -- Whether some function answers `h`; the case where none does comes first.
  by_cases answered : (h = [] ∨ (Queries X q).domain (h.map Prod.fst)) ∧
      ∃ g₀ : X → X, ∀ z ∈ h, z.2 = ⟨z.1.1, g₀ z.1.2⟩
  swap
  · -- No function answers `h` (more than `q` queries, or one input with two replies): the
    -- ideal probability is `0`, at most the real one.
    rw [Distribution.mass_eq_zero_of_forall_not _ fun g hg => answered ⟨hg.1, g, hg.2⟩,
      mul_zero]
    exact Distribution.uniform_nonNeg.mass_nonneg _
  -- Some function `g₀` answers `h`.
  obtain ⟨admitted, g₀, hg₀⟩ := answered
  let xs : List X := h.map fun z => z.1.2
  -- A function answers `h` if and only if it agrees with `g₀` at the inputs.
  have answers : ∀ f : X → X, (∀ z ∈ h, z.2 = ⟨z.1.1, f z.1.2⟩) ↔ ∀ x ∈ xs, f x = g₀ x := by
    intro f
    -- A statement on every input is one on every entry `z` of `h`, at its input.
    simp only [xs, List.forall_mem_map]
    refine forall₂_congr fun z hz => ?_
    -- The reply of `z` is `g₀` at its input, so `f` gives that reply if and only if it agrees
    -- with `g₀` there.
    rw [hg₀ z hz]
    simp [eq_comm]
  -- Both systems, as the probabilities of agreeing with `g₀` at the inputs.
  rw [Distribution.mass_congr _ fun g => (and_iff_right admitted).trans (answers g),
    Distribution.mass_congr _ fun (T : (X → X) × (X → X)) =>
      (and_iff_right admitted).trans (answers fun x => T.2 (T.1 x))]
  -- At most `q` distinct inputs: `h` is admitted, so it has at most `q` queries.
  have distinct : xs.toFinset.card ≤ q .eval := by
    refine (List.toFinset_card_le _).trans ?_
    have length := evaluation_length_le (q := q) (xs := h.map Prod.fst)
      (admitted.imp (fun empty => by simp [empty]) id)
    simpa [xs] using length
  -- The ideal system: a uniform `g` agrees with `g₀` at the `d` distinct inputs with
  -- probability `|X|^{-d}`.
  -- (The distinct points are the inputs themselves, the image of `id`, injective.)
  have ideal := Counting.uniform_mass_apply_list_eq (Y := X) xs id (Set.injOn_id _) g₀
  simp only [id] at ideal
  rw [ideal]
  -- No collision under `T₁` has probability at least `1 - q(q-1)/(2|X|)`: its complement, a
  -- collision, has probability at most `q(q-1)/(2|X|)`.
  have noCollision : 1 - (q .eval : ℝ) * ((q .eval : ℝ) - 1) / (2 * Fintype.card X) ≤
      (Distribution.uniform (X → X)).mass (fun T₁ => ¬ Collision T₁ xs) := by
    -- `Pr[collision] + Pr[no collision] = 1`, ...
    have total := Distribution.mass_add_compl (Distribution.uniform (X → X))
      (fun T₁ => Collision T₁ xs)
    rw [Distribution.weight_uniform] at total
    -- ... and `Pr[collision] ≤ q(q-1)/(2|X|)`, with at most `q` distinct inputs.
    linarith [collision_mass_le distinct]
  -- `(1 - q(q-1)/(2|X|)) |X|^{-d} ≤ Pr[no collision] |X|^{-d} ≤ Pr[T₂ ∘ T₁ agrees with g₀]`.
  calc _ ≤ (Distribution.uniform (X → X)).mass (fun T₁ => ¬ Collision T₁ xs) *
        (1 / (Fintype.card X : ℝ)) ^ xs.toFinset.card :=
        -- Multiplying `noCollision` by `|X|^{-d} ≥ 0`.
        mul_le_mul_of_nonneg_right noCollision (by positivity)
    _ ≤ _ :=
        -- The values of `T₂ ∘ T₁` at the inputs.
        composition_values_mass_ge xs g₀

/-- **The collision step, by the H-coefficient technique**: `T₂ ∘ T₁` is within
`q(q-1)/(2|X|)` of the uniform random function. -/
theorem composedURF_distance_le_hCoefficient (q : Evaluation.Port → ℕ) :
    Δ (composedURF X (q := q)) (URF (Queries X q)) ≤
      ENNReal.ofReal ((q .eval : ℝ) * ((q .eval : ℝ) - 1) / (2 * Fintype.card X)) := by
  -- The distance of two resources is the transcript distance of their random systems.
  rw [Interface.cc_distance_eq]
  -- The loss `q(q-1)/(2|X|)` is non-negative.
  have nonneg : 0 ≤ (q .eval : ℝ) * ((q .eval : ℝ) - 1) / (2 * Fintype.card X) :=
    div_nonneg (by simpa using natCast_mul_sub_one_le (Nat.zero_le (q .eval)) le_rfl)
      (by positivity)
  -- The H-coefficient bound without bad transcripts (`Bad := False`, `δ := 0`). Its arguments:
  -- both random systems reply at the queried interface (`.2` of a resource), the ratio holds
  -- at every transcript (`composedURF_ratio`), and no strategy produces a bad transcript.
  have bound := RandomSystem.transcriptDistance_le_of_ratio (composedURF X (q := q)).2
    (URF (Queries X q)).2 (fun _ => False) (δ := 0) nonneg
    (fun h _ => composedURF_ratio X q h)
    (fun _ _ _ _ => (Distribution.mass_eq_zero_of_forall_not _ fun _ bad => bad).le)
  -- `q(q-1)/(2|X|) + 0` is `q(q-1)/(2|X|)`.
  rwa [add_zero] at bound

/-! ### The collision step of the bonus -/

/-- **The self-composition `T ∘ T`** of a uniform random function. -/
def selfComposedURF {q : Evaluation.Port → ℕ} : Resource (Queries X q) :=
  Resource.sample (Distribution.uniform (X → X))
    fun T => Resource.ofFunction fun _ x => T (T x)

/-- **The collision game** of `T ∘ T`, with the hidden condition `SelfCollision`. -/
def sameKeyGame (q : Evaluation.Port → ℕ) :=
  PDG.ofSingleFunction (Queries X q).domain (Queries X q).nonempty_prefix
    (Queries X q).bound (Queries X q).length_le
    (Distribution.uniform (X → X)) (fun T x => T (T x))
    (fun T => ⟨SelfCollision T, fun {_ _} hp => selfCollision_monotone T hp⟩)

/-- Without a self-collision, the second-level values are values of `T` at fresh distinct
points, so `T ∘ T` has the law of the uniform random function. -/
lemma sameKeyGame_equiv (q : Evaluation.Port → ℕ) :
    sameKeyGame X q |≡ URF (Queries X q) := by
  classical
  -- The counting shifts the values of `T` in a group: `X` carries that of `Fin |X|`.
  have : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  let : AddCommGroup X := (Fintype.equivFin X).addCommGroup
  -- The uniform random function samples a uniform function once.
  rw [URF_perPort_eq]
  -- It suffices to factor at fixed inputs `xs` and prescribed values `answers`.
  apply PDG.ofSingleFunction_gameEquivalent
  intro xs answers
  -- A uniform function takes the values at the `d` distinct inputs with probability `|X|^{-d}`.
  have ideal := Counting.uniform_mass_apply_list_eq (Y := X) xs id (Set.injOn_id _) answers
  simp only [id] at ideal
  -- (Unfolding the factorization goal; `d` as the size of the set of distinct inputs.)
  dsimp only
  rw [ideal, ← Fintype.card_coe xs.toFinset]
  -- Without a self-collision, the points `T(x)` are distinct and outside the queried inputs, so
  -- `T` there is independent of `T` on the inputs: the values `T(T(x))` are `d` fresh uniform
  -- values, independent of the condition.
  rw [← Counting.uniform_mass_fresh_eq (ι := xs.toFinset) (↑xs.toFinset)
    (fun T => ¬ SelfCollision T xs) (fun T i => T i.1) ?_ ?_ ?_ (fun i => answers i.1)]
  · -- The values at the inputs, as a function on the distinct inputs.
    refine Distribution.mass_congr _ fun T => and_congr_left fun _ =>
      ⟨fun h => funext fun i => h i.1 (List.mem_toFinset.mp i.2),
        fun h x hx => congrFun h ⟨x, List.mem_toFinset.mpr hx⟩⟩
  · -- No self-collision depends only on `T` at the inputs.
    intro T T' hT
    have hT' : ∀ x ∈ xs, T x = T' x := fun x hx => hT x (List.mem_toFinset.mpr hx)
    simp only [SelfCollision, Collision]
    -- In each direction, transport a collision or a hit along the equal values at the inputs.
    constructor <;> rintro h (⟨x, hx, x', hx', hne, he⟩ | ⟨x, hx, hTx⟩)
    · exact h (.inl ⟨x, hx, x', hx', hne, by rw [hT' x hx, hT' x' hx', he]⟩)
    · exact h (.inr ⟨x, hx, by rwa [hT' x hx]⟩)
    · exact h (.inl ⟨x, hx, x', hx', hne, by rw [← hT' x hx, ← hT' x' hx', he]⟩)
    · exact h (.inr ⟨x, hx, by rwa [← hT' x hx]⟩)
  · -- The first-level points `T(x)` depend only on `T` at the inputs.
    intro T T' hT
    funext i
    exact hT i.1 i.2
  · -- Without a self-collision, the points `T(x)` are distinct (no collision) and none is an
    -- input.
    intro T hT
    refine ⟨fun i j h => Subtype.ext (by_contra fun hne => hT (.inl ⟨i.1,
      List.mem_toFinset.mp i.2, j.1, List.mem_toFinset.mp j.2, hne, h⟩)), fun i hi => hT (.inr
        ⟨i.1, List.mem_toFinset.mp i.2, List.mem_toFinset.mp hi⟩)⟩

/-- Blind winning is a self-collision among at most `q` fixed inputs: `q(q-1)/2` pairs and `q²`
first-level values hitting an input. -/
lemma sameKeyGame_blind_bound (q : Evaluation.Port → ℕ) :
    ν((sameKeyGame X q).blind (Queries X q).nonempty_prefix) ≤
      (q .eval : ℝ) * (3 * (q .eval : ℝ) - 1) / (2 * Fintype.card X) := by
  -- The bound `q(3q-1)/(2|X|)` is non-negative.
  have hq : 0 ≤ (q .eval : ℝ) * (3 * (q .eval : ℝ) - 1) := by
    simpa using natCast_mul_sub_one_le (Nat.zero_le (q .eval)) (by norm_num : (1 : ℝ) ≤ 3)
  -- A blind player fixes its inputs: bound the probability of a self-collision at every
  -- admitted list of inputs.
  apply PDG.ofFunction_blind_le (div_nonneg hq (by positivity))
  intro xs hxs
  -- The distinct inputs: at most `q`.
  let S := (xs.map Sigma.snd).toFinset
  have hS : S.card ≤ q .eval :=
    (List.toFinset_card_le _).trans ((List.length_map _).trans_le (evaluation_length_le hxs))
  -- The blind winning event at these inputs: a self-collision under `T`.
  change (Distribution.uniform (X → X)).mass
    (fun T => SelfCollision T (xs.map Sigma.snd)) ≤ _
  -- A collision: the union bound over the pairs of distinct inputs.
  have collision : (Distribution.uniform (X → X)).mass
      (fun T => Collision T (xs.map Sigma.snd)) ≤
        S.card * (S.card - 1) / 2 * (1 / Fintype.card X) := by
    calc _ = (Distribution.uniform (X → X)).mass
          (fun T => ∃ x ∈ S, ∃ x' ∈ S, x ≠ x' ∧ T x = T x') :=
          Distribution.mass_congr _ fun T => by simp [Collision, S]
      _ ≤ _ := Distribution.mass_exists_pair_le Distribution.uniform_nonNeg S _
          (fun _ _ _ h => h.symm) fun _ _ _ _ h => Counting.uniform_mass_apply_eq_le h
  -- A first-level value hitting an input: the union bound over the pairs (input, input), each
  -- with probability `1/|X|`.
  have hit : (Distribution.uniform (X → X)).mass
      (fun T => ∃ x ∈ xs.map Sigma.snd, T x ∈ xs.map Sigma.snd) ≤
        S.card * (S.card * (1 / Fintype.card X)) := by
    calc _ = (Distribution.uniform (X → X)).mass (fun T => ∃ x ∈ S, ∃ x' ∈ S, T x = x') :=
          Distribution.mass_congr _ fun T => by simp [S]
      _ ≤ ∑ x ∈ S, (Distribution.uniform (X → X)).mass (fun T => ∃ x' ∈ S, T x = x') :=
          Distribution.mass_exists_le Distribution.uniform_nonNeg _ _
      _ ≤ ∑ x ∈ S, ∑ x' ∈ S, (Distribution.uniform (X → X)).mass (fun T => T x = x') :=
          Finset.sum_le_sum fun _ _ => Distribution.mass_exists_le Distribution.uniform_nonNeg _ _
      _ ≤ ∑ x ∈ S, ∑ x' ∈ S, (1 / Fintype.card X : ℝ) :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ =>
            Counting.uniform_mass_coord_determined_le x id Function.injective_id (fun _ => x')
              (fun _ _ _ => rfl)
      _ = _ := by simp
  -- A self-collision is one or the other: the sum of the two bounds.
  refine ((Distribution.mass_or_le Distribution.uniform_nonNeg _ _).trans
    (add_le_add collision hit)).trans ?_
  -- `d(d-1)/(2|X|) + d²/|X| = d(3d-1)/(2|X|)`, at most `q(3q-1)/(2|X|)` since `d ≤ q`.
  have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc _ = (S.card : ℝ) * (3 * S.card - 1) / (2 * Fintype.card X) := by field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right
        (natCast_mul_sub_one_le hS (by norm_num : (1 : ℝ) ≤ 3)) (by positivity)

/-- **The collision step of the bonus**: `T ∘ T` is within `q(3q-1)/(2|X|)` of the uniform
random function. -/
theorem selfComposedURF_distance_le (q : Evaluation.Port → ℕ) :
    Δ (selfComposedURF X (q := q)) (URF (Queries X q)) ≤
      ENNReal.ofReal ((q .eval : ℝ) * (3 * (q .eval : ℝ) - 1) / (2 * Fintype.card X)) :=
  -- The game is conditionally equivalent to the uniform random function and presents
  -- `selfComposedURF` (`rfl`), so the distance is at most its blind winning probability
  -- [2, Theorem 4.17].
  ((sameKeyGame_equiv X q).game_dist_ofSingleFunction_le rfl).trans
    (ENNReal.ofReal_le_ofReal (sameKeyGame_blind_bound X q))

end

end ProofLadders.PRFCascade.PureSystems
