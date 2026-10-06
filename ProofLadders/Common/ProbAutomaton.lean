import ConstructiveCryptography.Source
import RandomSystems.Converter.ProgramAttachment
import ConstructiveCryptography.DSL.Converters
import ConstructiveCryptography.Context
import ProofLadders.Common.Programs
import ProofLadders.Common.Probability

/-!
# Probabilistic automata

A probabilistic automaton answers a query from its state with a law on the next state and the
reply. Its random system is given by the forward algorithm: the sub-law of the states after a
transcript, whose weight is the probability of the transcript (Maurer 2002, a random system
given by the conditional laws of its replies).

Two probabilistic automata are the same resource along a **simulation**: a kernel from the states
of one to those of the other, and an invariant of the inputs so far, such that at every query the
domain admits, a step of the second from the kernel image is a step of the first followed by the
kernel. A map of states is a point kernel; a kernel that samples a value not yet used defers its
sampling.

A deterministic automaton is the probabilistic automaton of its point steps, and a program
attached to an automaton is the program run against its steps, side by side automata run side by
side. A source table read in order is fresh sampling: the table after the reads `r` holds `r`,
then independent samples, and reading the next entry samples afresh. So a DSL component, compiled
to a program on sources, is the probabilistic automaton that samples afresh at each sampling
statement (`FreshSampling`): its presentation is built along the composition (sources, side by
side, programs, port-preserving programs, converters with their sources beside), and
`FreshSampling.eq_fresh` turns it into an equality. Equalities of DSL systems are then
simulations of their fresh-sampling automata.

Upstream candidates: `Distribution.bindK` and its lemmas, `pi_eq_bindK_update`, for
`Probability.Distribution`; `ProbStep`, `ProbStep.belief`, `RandomSystem.ofProbAutomaton`,
`ProbStep.SimulatesAt`, `ProbStep.belief_simulation`, `ProbStep.ofDeterministic`,
`ProbStep.parallel`, `Program.probInvoke`, `Program.probCombine` and their simulation lemmas, for
`RandomSystems.System`; `Interface.Resource.ofProbAutomaton` and its equalities, `SimulationOn`,
`FreshSampling`, for `ConstructiveCryptography.Automaton`.

## Main definitions

* `ProbStep S I X Y`: a probabilistic step
* `ProbStep.belief D step init h`: the forward algorithm
* `RandomSystem.ofProbAutomaton`, `Interface.Resource.ofProbAutomaton`: its random system and
  resource
* `ProbStep.SimulatesAt`, `SimulationOn E step₁ step₂`: a simulation step, and a simulation on a
  domain
* `ProbStep.ofDeterministic`, `ProbStep.parallel`, `Program.probCombine`, `ProbStep.fresh`: point
  steps, side by side, a program against a probabilistic step, fresh samples
* `FreshSampling B R`: a presentation of `R` as fresh sampling

## Main results

* `Interface.Resource.ofProbAutomaton_eq_of_simulation`, `ofProbAutomaton_eq_of_map`: equal
  resources along a simulation, and along a map of states
* `Interface.Resource.ofAutomaton_eq_ofProbAutomaton`: deterministic automata
* `Program.ofDeterministic_combine`, `ProbStep.ofDeterministic_parallelStep`: programs and side by
  side automata
* `ProbStep.simulatesAt_source`: a source table read in order is fresh sampling
* `SimulationOn.parallel`, `SimulationOn.ofProgram`, `SimulationOn.ofPreservingProgram`,
  `SimulationOn.ofLabelBoundedProgram`: simulations through the compositions, on their domains
* `FreshSampling.eq_fresh`, `Interface.Resource.source_eq_fresh`: a resource presented as fresh
  sampling is its fresh-sampling automaton
* `Interface.Resource.ofProbAutomaton_eq_of_mapOn`: equal resources along a map of states under an
  invariant
-/

namespace Probability.Distribution

open Classical

variable {A B C : Type*}

/-- **The mixture of a kernel** over a distribution: `∑ a, μ a • f a`. -/
noncomputable def bindK (μ : Distribution A) (f : A → Distribution B) : Distribution B :=
  Finsupp.linearCombination ℝ f μ

@[simp] lemma bindK_zero (f : A → Distribution B) : bindK 0 f = 0 :=
  map_zero _

@[simp] lemma bindK_single (a : A) (w : ℝ) (f : A → Distribution B) :
    bindK (Finsupp.single a w) f = w • f a :=
  Finsupp.linearCombination_single _ _ _

lemma bindK_add (μ ν : Distribution A) (f : A → Distribution B) :
    bindK (μ + ν) f = bindK μ f + bindK ν f :=
  map_add _ _ _

@[simp] lemma bindK_zero_right (μ : Distribution A) :
    bindK μ (fun _ => (0 : Distribution B)) = 0 := by
  induction μ using Finsupp.induction_linear with
  | zero => simp
  | add μ ν hμ hν => rw [bindK_add, hμ, hν, add_zero]
  | single a w => simp

lemma bindK_congr {μ : Distribution A} {f g : A → Distribution B}
    (h : ∀ a ∈ μ.support, f a = g a) : bindK μ f = bindK μ g := by
  unfold bindK
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  exact Finset.sum_congr rfl fun a ha => by
    show μ a • f a = μ a • g a
    rw [h a ha]

lemma bindK_add_right (μ : Distribution A) (f g : A → Distribution B) :
    bindK μ (fun a => f a + g a) = bindK μ f + bindK μ g := by
  induction μ using Finsupp.induction_linear with
  | zero => simp
  | add μ ν hμ hν => rw [bindK_add, bindK_add, bindK_add, hμ, hν]; abel
  | single a w => simp [smul_add]

lemma bindK_bindK (μ : Distribution A) (f : A → Distribution B) (g : B → Distribution C) :
    bindK (bindK μ f) g = bindK μ fun a => bindK (f a) g := by
  induction μ using Finsupp.induction_linear with
  | zero => simp
  | add μ ν hμ hν => rw [bindK_add, bindK_add, bindK_add, hμ, hν]
  | single a w => simp [bindK, map_smul]

/-- The point kernel leaves a distribution unchanged. -/
lemma bindK_single_one (μ : Distribution A) : bindK μ (fun a => Finsupp.single a 1) = μ := by
  induction μ using Finsupp.induction_linear with
  | zero => simp
  | add μ ν hμ hν => rw [bindK_add, hμ, hν]
  | single a w => simp

/-- A point kernel along `φ` is the pushforward along `φ`. -/
lemma bindK_single_comp (μ : Distribution A) (φ : A → B) :
    bindK μ (fun a => Finsupp.single (φ a) 1) = fTransform φ μ := by
  induction μ using Finsupp.induction_linear with
  | zero => simp [fTransform]
  | add μ ν hμ hν =>
    rw [bindK_add, hμ, hν]
    exact (Finsupp.mapDomain_add).symm
  | single a w => simp [fTransform]

lemma fTransform_bindK (φ : B → C) (μ : Distribution A) (f : A → Distribution B) :
    fTransform φ (bindK μ f) = bindK μ fun a => fTransform φ (f a) := by
  induction μ using Finsupp.induction_linear with
  | zero => simp [fTransform]
  | add μ ν hμ hν =>
    rw [bindK_add, bindK_add, ← hμ, ← hν]
    exact Finsupp.mapDomain_add
  | single a w =>
    rw [bindK_single, bindK_single]
    exact Finsupp.mapDomain_smul _ _

lemma bindK_fTransform (φ : A → B) (μ : Distribution A) (f : B → Distribution C) :
    bindK (fTransform φ μ) f = bindK μ (f ∘ φ) := by
  induction μ using Finsupp.induction_linear with
  | zero => simp [fTransform]
  | add μ ν hμ hν =>
    rw [show fTransform φ (μ + ν) = fTransform φ μ + fTransform φ ν from Finsupp.mapDomain_add,
      bindK_add, bindK_add, hμ, hν]
  | single a w => simp [fTransform]

lemma filter_bindK (p : B → Prop) (μ : Distribution A) (f : A → Distribution B) :
    (bindK μ f).filter p = bindK μ fun a => (f a).filter p := by
  induction μ using Finsupp.induction_linear with
  | zero => simp [Finsupp.filter_zero]
  | add μ ν hμ hν => rw [bindK_add, bindK_add, Finsupp.filter_add, hμ, hν]
  | single a w => simp [Finsupp.filter_smul]

lemma weight_bindK (μ : Distribution A) (f : A → Distribution B) :
    (bindK μ f).weight = μ.sum fun a w => w * (f a).weight := by
  induction μ using Finsupp.induction_linear with
  | zero => simp [weight]
  | add μ ν hμ hν =>
    rw [bindK_add, weight_add, hμ, hν,
      Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_mul _ _ _)]
  | single a w => simp [weight_smul]

/-- A kernel of weight one preserves the weight. -/
lemma weight_bindK_of_weight {μ : Distribution A} {f : A → Distribution B}
    (hf : ∀ a ∈ μ.support, (f a).weight = 1) : (bindK μ f).weight = μ.weight := by
  rw [weight_bindK, weight]
  exact Finset.sum_congr rfl fun a ha => by
    show μ a * (f a).weight = μ a
    rw [hf a ha, mul_one]

lemma bindK_nonNeg {μ : Distribution A} {f : A → Distribution B} (hμ : μ.NonNeg)
    (hf : ∀ a, (f a).NonNeg) : (bindK μ f).NonNeg := by
  intro b
  unfold bindK
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  exact Finset.sum_nonneg fun a _ => by
    simpa [Finsupp.smul_apply] using mul_nonneg (hμ a) (hf a b)

lemma mem_support_bindK {μ : Distribution A} {f : A → Distribution B} {b : B}
    (hb : b ∈ (bindK μ f).support) : ∃ a ∈ μ.support, b ∈ (f a).support := by
  by_contra hn
  push Not at hn
  apply Finsupp.mem_support_iff.mp hb
  unfold bindK
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun a ha => by
    simp [Finsupp.notMem_support_iff.mp (hn a ha)]

end Probability.Distribution

namespace Probability.Distribution

open Classical

variable {A B : Type*}

lemma bindK_apply (μ : Distribution A) (f : A → Distribution B) (b : B) :
    bindK μ f b = μ.sum fun a w => w * f a b := by
  unfold bindK
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  rfl

/-- A kernel that vanishes off an event is the kernel on the restriction to it. -/
lemma bindK_ite (μ : Distribution A) (P : A → Prop) (f : A → Distribution B) :
    bindK μ (fun a => if P a then f a else 0) = bindK (μ.restrict P) f := by
  induction μ using Finsupp.induction_linear with
  | zero => simp [restrict, Finsupp.filter_zero]
  | add μ ν hμ hν => rw [bindK_add, hμ, hν, ← bindK_add, restrict, restrict, restrict,
      Finsupp.filter_add]
  | single a w =>
    by_cases h : P a
    · simp [h, restrict, Finsupp.filter_single_of_pos _ h]
    · simp [h, restrict, Finsupp.filter_single_of_neg _ h]

lemma restrict_bindK (P : B → Prop) (μ : Distribution A) (f : A → Distribution B) :
    (bindK μ f).restrict P = bindK μ fun a => (f a).restrict P :=
  filter_bindK P μ f

lemma support_restrict_subset (μ : Distribution A) (P : A → Prop) :
    (μ.restrict P).support ⊆ μ.support := fun a ha => by
  rw [Finsupp.mem_support_iff, restrict_apply] at ha
  rw [Finsupp.mem_support_iff]
  split_ifs at ha
  · exact ha
  · exact absurd rfl ha

lemma restrict_fTransform (f : A → B) (μ : Distribution A) (P : B → Prop) :
    (fTransform f μ).restrict P = fTransform f (μ.restrict fun a => P (f a)) := by
  induction μ using Finsupp.induction_linear with
  | zero => simp [restrict, fTransform, Finsupp.filter_zero]
  | add μ ν hμ hν =>
    rw [show fTransform f (μ + ν) = fTransform f μ + fTransform f ν from Finsupp.mapDomain_add,
      restrict, Finsupp.filter_add, ← restrict, ← restrict, hμ, hν, restrict, restrict, restrict,
      Finsupp.filter_add]
    exact Finsupp.mapDomain_add.symm
  | single a w =>
    have hs : fTransform f (Finsupp.single a w) = Finsupp.single (f a) w := Finsupp.mapDomain_single
    by_cases h : P (f a)
    · rw [hs, restrict, restrict, Finsupp.filter_single_of_pos _ h,
        Finsupp.filter_single_of_pos (fun a => P (f a)) h, hs]
    · rw [hs, restrict, restrict, Finsupp.filter_single_of_neg _ h,
        Finsupp.filter_single_of_neg (fun a => P (f a)) h]
      simp [fTransform]

lemma restrict_restrict (μ : Distribution A) (P Q : A → Prop) :
    (μ.restrict P).restrict Q = μ.restrict fun a => P a ∧ Q a := by
  ext a
  simp only [restrict_apply]
  by_cases hP : P a <;> by_cases hQ : Q a <;> simp [hP, hQ]

lemma restrict_congr (μ : Distribution A) {P Q : A → Prop} (h : ∀ a, P a ↔ Q a) :
    μ.restrict P = μ.restrict Q := by
  ext a
  simp only [restrict_apply, h]

lemma restrict_false (μ : Distribution A) : μ.restrict (fun _ => False) = 0 := by
  ext a
  simp

lemma single_restrict (a : A) (w : ℝ) (P : A → Prop) :
    Distribution.restrict (Finsupp.single a w : Distribution A) P =
      if P a then Finsupp.single a w else 0 := by
  by_cases h : P a
  · simp [restrict, Finsupp.filter_single_of_pos _ h, h]
  · simp [restrict, Finsupp.filter_single_of_neg _ h, h]

/-- The pushforward of a point mass. -/
lemma fTransform_single (f : A → B) (a : A) (w : ℝ) :
    fTransform f (Finsupp.single a w) = Finsupp.single (f a) w :=
  Finsupp.mapDomain_single

/-- Pushforward as a point kernel. -/
lemma fTransform_eq_bindK (φ : A → B) (μ : Distribution A) :
    fTransform φ μ = bindK μ fun a => Finsupp.single (φ a) 1 :=
  (bindK_single_comp μ φ).symm

/-- **Independent mixtures commute.** -/
lemma bindK_comm {C : Type*} (μ : Distribution A) (ν : Distribution B)
    (F : A → B → Distribution C) :
    (bindK μ fun a => bindK ν fun b => F a b) = bindK ν fun b => bindK μ fun a => F a b := by
  induction μ using Finsupp.induction_linear with
  | zero => simp
  | add μ₁ μ₂ h₁ h₂ =>
    rw [bindK_add, h₁, h₂, ← bindK_add_right]
    exact bindK_congr fun b _ => (bindK_add _ _ _).symm
  | single a w =>
    rw [bindK_single]
    induction ν using Finsupp.induction_linear with
    | zero => simp
    | add ν₁ ν₂ h₁ h₂ =>
      rw [bindK_add, bindK_add, smul_add, h₁, h₂]
    | single b v => simp [smul_smul, mul_comm]

lemma fTransform_congr_support {f g : A → B} {μ : Distribution A}
    (h : ∀ a ∈ μ.support, f a = g a) : fTransform f μ = fTransform g μ := by
  rw [fTransform_eq_bindK, fTransform_eq_bindK]
  exact bindK_congr fun a ha => by rw [h a ha]

/-- **Disintegration of an independent product** at one coordinate: sample that coordinate first,
then the product with that coordinate fixed. -/
lemma pi_eq_bindK_update {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Distribution A)
    (n : ι) : pi μ = bindK (μ n) fun z => pi (Function.update μ n (Finsupp.single z 1)) := by
  ext t
  have hrest : ∀ z : A, (∏ i, Function.update μ n (Finsupp.single z 1) i (t i)) =
      (Finsupp.single z (1 : ℝ)) (t n) * ∏ i ∈ Finset.univ.erase n, μ i (t i) := by
    intro z
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ n), Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [pi_apply, bindK_apply]
  simp only [pi_apply, hrest, Finsupp.single_apply]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ n), Finsupp.sum]
  simp only [← mul_assoc, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.mp h, zero_mul]

lemma eq_of_mem_support_pi_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Distribution A) (n : ι) (z : A) {t : ι → A}
    (ht : t ∈ (pi (Function.update μ n (Finsupp.single z 1))).support) : t n = z := by
  rw [Finsupp.mem_support_iff, pi_apply] at ht
  by_contra hne
  apply ht
  refine Finset.prod_eq_zero (Finset.mem_univ n) ?_
  rw [Function.update_self, Finsupp.single_apply, if_neg (Ne.symm hne)]

/-- An independent product as a mixture. -/
lemma prod_eq_bindK (μ : Distribution A) (ν : Distribution B) :
    prod μ ν = bindK μ fun a => fTransform (fun b => (a, b)) ν := by
  ext ⟨a, b⟩
  rw [prod_apply, bindK_apply, Finsupp.sum]
  have hpt : ∀ a', fTransform (fun b' => (a', b')) ν (a, b) = if a' = a then ν b else 0 := by
    intro a'
    rw [fTransform_apply_eq_mass]
    split_ifs with h
    · subst h
      rw [mass, Finsupp.sum]
      simp only [Prod.mk.injEq, true_and]
      rw [Finset.sum_ite_eq']
      split_ifs with hb
      · rfl
      · exact (Finsupp.notMem_support_iff.mp hb).symm
    · exact mass_eq_zero_of_forall_not _ fun b' h' => h (Prod.mk.inj h').1
  simp only [hpt, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with ha
  · rfl
  · rw [Finsupp.notMem_support_iff.mp ha, zero_mul]

lemma support_fTransform_subset [DecidableEq B] (f : A → B) (μ : Distribution A) :
    (fTransform f μ).support ⊆ μ.support.image f :=
  Finsupp.mapDomain_support

/-- The first components of a pushforward along `(·, c)`, restricted to second component `y`. -/
lemma fTransform_fst_restrict_pair {C : Type*} (ν : Distribution A) (c y : C) :
    fTransform Prod.fst ((fTransform (fun a => (a, c)) ν).restrict fun p => p.2 = y) =
      if c = y then ν else 0 := by
  split_ifs with h
  · subst h
    rw [show (fTransform (fun a => (a, c)) ν).restrict (fun p => p.2 = c) =
        fTransform (fun a => (a, c)) ν by
      ext p
      rw [restrict_apply]
      split_ifs with hp
      · rfl
      · rw [fTransform_apply_eq_mass]
        exact (mass_eq_zero_of_forall_not _ fun a ha => hp (by rw [← ha])).symm,
      fTransform_fTransform]
    exact Finsupp.mapDomain_id
  · rw [show (fTransform (fun a => (a, c)) ν).restrict (fun p => p.2 = y) = 0 by
      ext p
      rw [restrict_apply]
      split_ifs with hp
      · rw [fTransform_apply_eq_mass]
        exact mass_eq_zero_of_forall_not _ fun a ha => h (by rw [← hp, ← ha])
      · rfl]
    simp [fTransform]

end Probability.Distribution

namespace SystemAlgebra

open Probability Probability.Distribution Classical

/-- **A probabilistic step**: from a state and a query at the label `i`, a law on the next state
and the reply at `i`. -/
abbrev ProbStep (S I : Type) (X Y : I → Type) :=
  S → (i : I) → X i → Distribution.ProbDist (S × Y i)

namespace ProbStep

variable {S I : Type} {X Y : I → Type} (step : ProbStep S I X Y)

/-- The next state with the reply at the queried label. -/
def tagged (x : Σ i, X i) (sy : S × Y x.1) : S × Σ i, Y i := (sy.1, ⟨x.1, sy.2⟩)

/-- The law of the next state and the reply to the query `x` in the state `s`. -/
noncomputable def outcome (s : S) (x : Σ i, X i) : Distribution (S × Σ i, Y i) :=
  fTransform (tagged x) (step s x.1 x.2).1

lemma outcome_nonNeg (s : S) (x : Σ i, X i) : (step.outcome s x).NonNeg :=
  (step s x.1 x.2).2.1.fTransform _

lemma weight_outcome (s : S) (x : Σ i, X i) : (step.outcome s x).weight = 1 := by
  rw [outcome, weight_fTransform]
  exact (step s x.1 x.2).2.2

/-- **The transition** of a state law on a query and its reply: the states reached with that
reply. -/
noncomputable def transition (β : Distribution S) (x : Σ i, X i) (y : Σ i, Y i) :
    Distribution S :=
  bindK β fun s => fTransform Prod.fst ((step.outcome s x).restrict fun sy => sy.2 = y)

/-- The law of the reply to the query `x` from the state law `β`. -/
noncomputable def replyLaw (β : Distribution S) (x : Σ i, X i) : Distribution (Σ i, Y i) :=
  bindK β fun s => fTransform Prod.snd (step.outcome s x)

lemma weight_transition (β : Distribution S) (x : Σ i, X i) (y : Σ i, Y i) :
    (step.transition β x y).weight = β.sum fun s w => w * (step.outcome s x).mass (·.2 = y) := by
  rw [transition, weight_bindK]
  simp only [weight_fTransform, weight_restrict]

lemma replyLaw_apply (β : Distribution S) (x : Σ i, X i) (y : Σ i, Y i) :
    step.replyLaw β x y = (step.transition β x y).weight := by
  rw [weight_transition, replyLaw, bindK_apply]
  simp only [fTransform_apply_eq_mass]

lemma weight_replyLaw (β : Distribution S) (x : Σ i, X i) :
    (step.replyLaw β x).weight = β.weight := by
  rw [replyLaw, weight_bindK_of_weight fun s _ => by rw [weight_fTransform, weight_outcome]]

lemma transition_nonNeg {β : Distribution S} (hβ : β.NonNeg) (x : Σ i, X i) (y : Σ i, Y i) :
    (step.transition β x y).NonNeg :=
  bindK_nonNeg hβ fun s => ((step.outcome_nonNeg s x).restrict _).fTransform _

/-- A reply at another label than the queried one is impossible. -/
lemma transition_eq_zero {β : Distribution S} {x : Σ i, X i} {y : Σ i, Y i} (hy : y.1 ≠ x.1) :
    step.transition β x y = 0 := by
  rw [transition]
  refine (bindK_congr fun s _ => ?_).trans (bindK_zero_right β)
  have hr : (step.outcome s x).restrict (fun sy => sy.2 = y) = 0 := by
    ext sy
    rw [restrict_apply]
    split_ifs with h
    · rw [outcome, fTransform_apply_eq_mass]
      exact mass_eq_zero_of_forall_not _ fun a ha => hy (by rw [← h, ← ha]; rfl)
    · rfl
  rw [hr]
  rfl

variable (D : Domain (Σ i, X i) (Σ i, Y i)) (init : Distribution S)

/-- The forward algorithm on a reversed transcript. -/
noncomputable def beliefRev : List ((Σ i, X i) × (Σ i, Y i)) → Distribution S
  | [] => init
  | e :: rh => if D rh.reverse e.1 then step.transition (beliefRev rh) e.1 e.2 else 0

/-- **The forward algorithm**: the sub-law of the states after the transcript `h`, zero once a
query is outside the domain. -/
noncomputable def belief (h : List ((Σ i, X i) × (Σ i, Y i))) : Distribution S :=
  step.beliefRev D init h.reverse

@[simp] lemma belief_nil : step.belief D init [] = init := rfl

lemma belief_snoc (h : List ((Σ i, X i) × (Σ i, Y i))) (x : Σ i, X i) (y : Σ i, Y i) :
    step.belief D init (h ++ [(x, y)]) =
      if D h x then step.transition (step.belief D init h) x y else 0 := by
  simp [belief, beliefRev, List.reverse_append]

lemma belief_nonNeg (hinit : init.NonNeg) (h : List ((Σ i, X i) × (Σ i, Y i))) :
    (step.belief D init h).NonNeg := by
  induction h using List.reverseRecOn with
  | nil => exact hinit
  | append_singleton h e ih =>
    rw [belief_snoc]
    split_ifs
    · exact step.transition_nonNeg ih _ _
    · exact fun _ => le_rfl

end ProbStep

variable {S I : Type} {X Y : I → Type} [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)]

/-- **The random system of a probabilistic automaton** with its initial state sampled from
`init`: the probability of a transcript is the weight of the forward algorithm. -/
noncomputable def RandomSystem.ofProbAutomaton (D : Domain (Σ i, X i) (Σ i, Y i))
    (step : ProbStep S I X Y) (init : Distribution.ProbDist S) :
    RandomSystem (Σ i, X i) (Σ i, Y i) D :=
  ⟨fun h => (step.belief D init.1 h).weight, init.2.2,
    fun h => (step.belief_nonNeg D init.1 init.2.1 h).weight_nonneg, fun h x =>
    ⟨if D h x then step.replyLaw (step.belief D init.1 h) x else 0, fun y => by
      show _ = (step.belief D init.1 (h ++ [(x, y)])).weight
      rw [step.belief_snoc]
      split_ifs
      · exact step.replyLaw_apply _ _ _
      · simp [weight], by
      split_ifs
      · exact step.weight_replyLaw _ _
      · simp [weight]⟩⟩

lemma RandomSystem.ofProbAutomaton_apply (D : Domain (Σ i, X i) (Σ i, Y i))
    (step : ProbStep S I X Y) (init : Distribution.ProbDist S)
    (h : List ((Σ i, X i) × (Σ i, Y i))) :
    RandomSystem.ofProbAutomaton D step init h = (step.belief D init.1 h).weight := rfl

lemma RandomSystem.ofProbAutomaton_repliesAtQueriedInterface (D : Domain (Σ i, X i) (Σ i, Y i))
    (step : ProbStep S I X Y) (init : Distribution.ProbDist S) :
    (RandomSystem.ofProbAutomaton D step init).RepliesAtQueriedInterface := by
  intro h x y hy
  rw [ofProbAutomaton_apply, step.belief_snoc]
  split_ifs
  · rw [step.transition_eq_zero hy]
    simp [weight]
  · simp [weight]

/-- **The resource of a probabilistic automaton** with its initial state sampled from `init`. -/
noncomputable def Interface.Resource.ofProbAutomaton (T : Interface) (step : ProbStep S T.I T.X T.Y)
    (init : Distribution.ProbDist S) : Interface.Resource T :=
  ⟨RandomSystem.ofProbAutomaton T.inputDomain step init,
    RandomSystem.ofProbAutomaton_repliesAtQueriedInterface _ _ _⟩

namespace ProbStep

variable {S₁ S₂ : Type} (step₁ : ProbStep S₁ I X Y) (step₂ : ProbStep S₂ I X Y)

/-- **A simulation step** of `step₁` by `step₂` along the kernel `K`, at the state `s` and the
query `x`: from `K s` a step of `step₂` is a step of `step₁` from `s` followed by `K`, with the
same reply. -/
def SimulatesAt (K : S₁ → Distribution.ProbDist S₂) (s : S₁) (x : Σ i, X i) : Prop :=
  bindK (K s).1 (fun s₂ => step₂.outcome s₂ x) =
    bindK (step₁.outcome s x) fun p => fTransform (fun s₂ => (s₂, p.2)) (K p.1).1

omit [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] in
/-- Along simulation steps, the transition of the kernel image is the kernel image of the
transition. -/
lemma transition_bindK {K : S₁ → Distribution.ProbDist S₂} {β : Distribution S₁}
    {x : Σ i, X i} (hsim : ∀ s ∈ β.support, SimulatesAt step₁ step₂ K s x) (y : Σ i, Y i) :
    step₂.transition (bindK β fun s => (K s).1) x y =
      bindK (step₁.transition β x y) fun s => (K s).1 := by
  rw [transition, transition, bindK_bindK, bindK_bindK]
  refine bindK_congr fun s hs => ?_
  have hpush : (bindK (K s).1 fun s₂ =>
      fTransform Prod.fst ((step₂.outcome s₂ x).restrict fun sy => sy.2 = y)) =
      fTransform Prod.fst ((bindK (K s).1 fun s₂ => step₂.outcome s₂ x).restrict
        fun sy => sy.2 = y) := by
    rw [restrict_bindK, fTransform_bindK]
  have h := hsim s hs
  unfold SimulatesAt at h
  rw [hpush, h, restrict_bindK, fTransform_bindK]
  simp only [fTransform_fst_restrict_pair]
  rw [bindK_ite, bindK_fTransform]
  rfl

omit [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] in
/-- **The forward algorithm along a simulation**: the invariant holds after each transcript in
the domain, and the state law of `step₂` is the kernel image of that of `step₁`. -/
lemma belief_simulation (E : List (Σ i, X i) → Prop) (bound : ℕ)
    (hE : ∀ h, E h → h.length ≤ bound) (K : S₁ → Distribution.ProbDist S₂)
    (inv : List (Σ i, X i) → S₁ → Prop)
    (hpres : ∀ xs s x, inv xs s → E (xs ++ [x]) →
      ∀ p ∈ (step₁.outcome s x).support, inv (xs ++ [x]) p.1)
    (hsim : ∀ xs s x, inv xs s → E (xs ++ [x]) → SimulatesAt step₁ step₂ K s x)
    (init : Distribution S₁) (hinit : ∀ s ∈ init.support, inv [] s)
    (h : List ((Σ i, X i) × (Σ i, Y i))) :
    (∀ s ∈ (step₁.belief (Domain.ofInputs E bound hE) init h).support, inv (h.map Prod.fst) s) ∧
      step₂.belief (Domain.ofInputs E bound hE) (bindK init fun s => (K s).1) h =
        bindK (step₁.belief (Domain.ofInputs E bound hE) init h) fun s => (K s).1 := by
  induction h using List.reverseRecOn with
  | nil => exact ⟨hinit, rfl⟩
  | append_singleton h e ih =>
    obtain ⟨x, y⟩ := e
    rw [belief_snoc, belief_snoc]
    split_ifs with hd
    · have hd' : E (h.map Prod.fst ++ [x]) := hd
      refine ⟨fun s hs => ?_, ?_⟩
      · obtain ⟨s₀, hs₀, hs⟩ := mem_support_bindK hs
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (support_fTransform_subset _ _ hs)
        have hp' : p ∈ (step₁.outcome s₀ x).support := support_restrict_subset _ _ hp
        simpa using hpres _ _ x (ih.1 s₀ hs₀) hd' p hp'
      · rw [ih.2]
        exact transition_bindK step₁ step₂ (fun s hs => hsim _ s x (ih.1 s hs) hd') y
    · exact ⟨fun s hs => absurd hs (by simp), by simp⟩

end ProbStep

/-- **Equal resources along a simulation**: if `step₂` simulates `step₁` along `K` at the states
satisfying an invariant of the inputs so far, at every query the domain admits, and the initial
law of `step₂` is the kernel image of that of `step₁`, the probabilistic automata are the same
resource. -/
lemma Interface.Resource.ofProbAutomaton_eq_of_simulation {T : Interface} {S₁ S₂ : Type}
    (step₁ : ProbStep S₁ T.I T.X T.Y) (step₂ : ProbStep S₂ T.I T.X T.Y)
    (init₁ : Distribution.ProbDist S₁) (init₂ : Distribution.ProbDist S₂)
    (K : S₁ → Distribution.ProbDist S₂) (inv : List (Σ i, T.X i) → S₁ → Prop)
    (hinit : ∀ s ∈ init₁.1.support, inv [] s)
    (hpres : ∀ xs s x, inv xs s → T.domain (xs ++ [x]) →
      ∀ p ∈ (step₁.outcome s x).support, inv (xs ++ [x]) p.1)
    (hsim : ∀ xs s x, inv xs s → T.domain (xs ++ [x]) → ProbStep.SimulatesAt step₁ step₂ K s x)
    (hK : init₂.1 = bindK init₁.1 fun s => (K s).1) :
    Interface.Resource.ofProbAutomaton T step₁ init₁ =
      Interface.Resource.ofProbAutomaton T step₂ init₂ := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  have hb := (ProbStep.belief_simulation step₁ step₂ T.domain T.bound T.length_le K inv hpres
    hsim init₁.1 hinit h).2
  rw [← hK] at hb
  show RandomSystem.ofProbAutomaton _ step₁ init₁ h = RandomSystem.ofProbAutomaton _ step₂ init₂ h
  rw [RandomSystem.ofProbAutomaton_apply, RandomSystem.ofProbAutomaton_apply]
  change (step₁.belief (Domain.ofInputs T.domain T.bound T.length_le) init₁.1 h).weight =
    (step₂.belief (Domain.ofInputs T.domain T.bound T.length_le) init₂.1 h).weight
  rw [hb, weight_bindK_of_weight fun s _ => (K s).2.2]

/-- **Equal resources along a map of states**: if the steps of `step₂` from `φ s` are those of
`step₁` from `s` with the next state mapped by `φ`, and the initial laws correspond, the
probabilistic automata are the same resource. -/
lemma Interface.Resource.ofProbAutomaton_eq_of_map {T : Interface} {S₁ S₂ : Type}
    (step₁ : ProbStep S₁ T.I T.X T.Y) (step₂ : ProbStep S₂ T.I T.X T.Y)
    (init₁ : Distribution.ProbDist S₁) (init₂ : Distribution.ProbDist S₂) (φ : S₁ → S₂)
    (hstep : ∀ s x, step₂.outcome (φ s) x = fTransform (Prod.map φ id) (step₁.outcome s x))
    (hinit : init₂.1 = fTransform φ init₁.1) :
    Interface.Resource.ofProbAutomaton T step₁ init₁ =
      Interface.Resource.ofProbAutomaton T step₂ init₂ := by
  refine Interface.Resource.ofProbAutomaton_eq_of_simulation step₁ step₂ init₁ init₂
    (fun s => Distribution.ProbDist.single (φ s)) (fun _ _ => True) (fun _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial) (fun _ s x _ _ => ?_) ?_
  · unfold ProbStep.SimulatesAt
    simp only [Distribution.ProbDist.single, bindK_single, one_smul]
    rw [hstep, ← bindK_single_comp]
    refine bindK_congr fun p _ => ?_
    simp [fTransform]
    rfl
  · rw [hinit]
    exact (bindK_single_comp _ _).symm


namespace ProbStep

/-- **The probabilistic step of a deterministic automaton**: the point law of its step. -/
noncomputable def ofDeterministic (step : S → (i : I) → X i → S × Y i) : ProbStep S I X Y :=
  fun s i x => Distribution.ProbDist.single (step s i x)

omit [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] in
lemma outcome_ofDeterministic (step : S → (i : I) → X i → S × Y i) (s : S) (x : Σ i, X i) :
    (ofDeterministic step).outcome s x =
      Finsupp.single ((step s x.1 x.2).1, (⟨x.1, (step s x.1 x.2).2⟩ : Σ i, Y i)) 1 := by
  simp [outcome, ofDeterministic, Distribution.ProbDist.single, fTransform, tagged]

omit [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] in
lemma transition_ofDeterministic (step : S → (i : I) → X i → S × Y i) (β : Distribution S)
    (x : Σ i, X i) (y : Σ i, Y i) :
    (ofDeterministic step).transition β x y = fTransform (fun s => (step s x.1 x.2).1)
      (β.restrict fun s => (⟨x.1, (step s x.1 x.2).2⟩ : Σ i, Y i) = y) := by
  rw [transition]
  simp only [outcome_ofDeterministic, single_restrict]
  rw [← bindK_single_comp, ← bindK_ite]
  refine bindK_congr fun s _ => ?_
  split_ifs <;> simp [fTransform]

omit [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] in
/-- **The forward algorithm of a deterministic automaton** on an input domain: the initial states
from which the automaton gives the transcript, moved to the state they reach. -/
lemma belief_ofDeterministic (step : S → (i : I) → X i → S × Y i) (E : List (Σ i, X i) → Prop)
    (bound : ℕ) (hE : ∀ h, E h → h.length ≤ bound) (init : Distribution S)
    (h : List ((Σ i, X i) × (Σ i, Y i))) :
    (ofDeterministic step).belief (Domain.ofInputs E bound hE) init h =
      fTransform (fun s => stateAfter step s (h.map Prod.fst)) (init.restrict fun s =>
        Replies (filterDom E (automatonSystem step s)) (h.map Prod.fst) (h.map Prod.snd)) := by
  induction h using List.reverseRecOn with
  | nil =>
    simp only [belief_nil, List.map_nil, stateAfter_nil, replies_nil]
    rw [show (fTransform (fun s => s) (init.restrict fun _ => True)) = init by
      rw [show (init.restrict fun _ => True) = init by ext; simp]
      exact Finsupp.mapDomain_id]
  | append_singleton h e ih =>
    obtain ⟨x, y⟩ := e
    have hrep : ∀ s, Replies (filterDom E (automatonSystem step s)) ((h ++ [(x, y)]).map Prod.fst)
        ((h ++ [(x, y)]).map Prod.snd) ↔
          Replies (filterDom E (automatonSystem step s)) (h.map Prod.fst) (h.map Prod.snd) ∧
            E (h.map Prod.fst ++ [x]) ∧
              (⟨x.1, (step (stateAfter step s (h.map Prod.fst)) x.1 x.2).2⟩ : Σ i, Y i) = y := by
      intro s
      simp only [List.map_append, List.map_cons, List.map_nil, replies_snoc,
        SystemAlgebra.filterDom, automatonSystem_snoc]
      by_cases hx : E (h.map Prod.fst ++ [x])
      · simp [hx, Part.some_inj, eq_comm]
      · simp [hx, Part.none_ne_some]
    rw [belief_snoc, restrict_congr init hrep]
    split_ifs with hd
    · rw [ih, transition_ofDeterministic, restrict_fTransform, fTransform_fTransform,
        restrict_restrict]
      have hd' : E (h.map Prod.fst ++ [x]) := hd
      simp only [List.map_append, List.map_cons, List.map_nil, stateAfter_snoc]
      congr 1
      exact restrict_congr init fun s => by simp [hd']
    · have hd' : ¬ E (h.map Prod.fst ++ [x]) := hd
      rw [restrict_congr init (Q := fun _ => False) fun s => by simp [hd'], restrict_false]
      simp [fTransform]

end ProbStep

/-- **A deterministic automaton is a probabilistic automaton** whose steps are point laws. -/
lemma Interface.Resource.ofAutomaton_eq_ofProbAutomaton (T : Interface)
    (step : S → (i : T.I) → T.X i → S × T.Y i) (initial : Distribution.ProbDist S) :
    Interface.Resource.ofAutomaton T step initial =
      Interface.Resource.ofProbAutomaton T (ProbStep.ofDeterministic step) initial := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [Interface.Resource.ofAutomaton_mass]
  show _ = RandomSystem.ofProbAutomaton _ _ _ h
  rw [RandomSystem.ofProbAutomaton_apply, ProbStep.belief_ofDeterministic, weight_fTransform,
    weight_restrict]

namespace ProbStep

/-- The identity kernel. -/
noncomputable def idKernel (S : Type) : S → Distribution.ProbDist S := Distribution.ProbDist.single

lemma idKernel_val (s : S) : (idKernel S s).1 = Finsupp.single s 1 := rfl

omit [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] in
/-- **Every step simulates itself** along the identity kernel. -/
lemma simulatesAt_refl (step : ProbStep S I X Y) (s : S) (x : Σ i, X i) :
    SimulatesAt step step (idKernel S) s x := by
  unfold SimulatesAt
  simp only [idKernel_val]
  rw [bindK_single, one_smul]
  conv_lhs => rw [← bindK_single_one (step.outcome s x)]
  refine bindK_congr fun p _ => ?_
  simp [fTransform]

section Parallel

variable {T J : Type} {X₁ Y₁ : I → Type} {X₂ Y₂ : J → Type}

/-- **Two probabilistic automata side by side.** -/
noncomputable def parallel (f : ProbStep S I X₁ Y₁) (g : ProbStep T J X₂ Y₂) :
    ProbStep (S × T) (I ⊕ J) (Sum.rec X₁ X₂) (Sum.rec Y₁ Y₂)
  | (a, b), .inl i, x => ⟨fTransform (fun sy => ((sy.1, b), sy.2)) (f a i x).1,
      fTransform_isProbDist _ (f a i x).2⟩
  | (a, b), .inr j, x => ⟨fTransform (fun ty => ((a, ty.1), ty.2)) (g b j x).1,
      fTransform_isProbDist _ (g b j x).2⟩

/-- The reply of the left automaton, at the left label. -/
def inlReply : (Σ i, Y₁ i) → Σ l, Sum.rec (motive := fun _ => Type) Y₁ Y₂ l :=
  fun y => ⟨.inl y.1, y.2⟩

/-- The reply of the right automaton, at the right label. -/
def inrReply : (Σ j, Y₂ j) → Σ l, Sum.rec (motive := fun _ => Type) Y₁ Y₂ l :=
  fun y => ⟨.inr y.1, y.2⟩

lemma outcome_parallel_inl (f : ProbStep S I X₁ Y₁) (g : ProbStep T J X₂ Y₂) (a : S) (b : T)
    (i : I) (x : X₁ i) :
    (parallel f g).outcome (a, b) ⟨.inl i, x⟩ =
      fTransform (fun p => ((p.1, b), inlReply p.2)) (f.outcome a ⟨i, x⟩) := by
  simp only [outcome, parallel, fTransform_fTransform]
  rfl

lemma outcome_parallel_inr (f : ProbStep S I X₁ Y₁) (g : ProbStep T J X₂ Y₂) (a : S) (b : T)
    (j : J) (x : X₂ j) :
    (parallel f g).outcome (a, b) ⟨.inr j, x⟩ =
      fTransform (fun p => ((a, p.1), inrReply p.2)) (g.outcome b ⟨j, x⟩) := by
  simp only [outcome, parallel, fTransform_fTransform]
  rfl

lemma ofDeterministic_parallelStep (f : S → (i : I) → X₁ i → S × Y₁ i)
    (g : T → (j : J) → X₂ j → T × Y₂ j) :
    ofDeterministic (parallelStep f g) = parallel (ofDeterministic f) (ofDeterministic g) := by
  funext st l x
  obtain ⟨a, b⟩ := st
  apply Subtype.ext
  cases l <;>
    simp [parallel, ofDeterministic, parallelStep, Distribution.ProbDist.single, fTransform]

/-- The product of two kernels. -/
noncomputable def prodKernel {S₁ T₁ S₂ T₂ : Type} (K₁ : S₁ → Distribution.ProbDist S₂)
    (K₂ : T₁ → Distribution.ProbDist T₂) (st : S₁ × T₁) : Distribution.ProbDist (S₂ × T₂) :=
  ⟨bindK (K₁ st.1).1 fun a => fTransform (fun b => (a, b)) (K₂ st.2).1,
    ⟨bindK_nonNeg (K₁ st.1).2.1 fun _ => (K₂ st.2).2.1.fTransform _, by
      rw [weight_bindK_of_weight fun a _ => by rw [weight_fTransform]; exact (K₂ st.2).2.2]
      exact (K₁ st.1).2.2⟩⟩

omit [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] in
/-- Two independent pushforwards into pairs commute. -/
lemma bindK_fTransform_pair_comm {A B C : Type} (μ : Distribution A) (ν : Distribution B)
    (r : C) :
    (bindK ν fun b => fTransform (fun a => ((a, b), r)) μ) =
      bindK μ fun a => fTransform (fun b => ((a, b), r)) ν := by
  simp only [fTransform_eq_bindK]
  exact bindK_comm ν μ fun b a => Finsupp.single ((a, b), r) 1

lemma prodKernel_val {S₁ T₁ S₂ T₂ : Type} (K₁ : S₁ → Distribution.ProbDist S₂)
    (K₂ : T₁ → Distribution.ProbDist T₂) (st : S₁ × T₁) :
    (prodKernel K₁ K₂ st).1 = prod (K₁ st.1).1 (K₂ st.2).1 :=
  (prod_eq_bindK _ _).symm

/-- **A simulation step side by side, at the left automaton.** -/
lemma simulatesAt_parallel_inl {S₁ T₁ S₂ T₂ : Type} {f₁ : ProbStep S₁ I X₁ Y₁}
    {f₂ : ProbStep S₂ I X₁ Y₁} (g₁ : ProbStep T₁ J X₂ Y₂) (g₂ : ProbStep T₂ J X₂ Y₂)
    {K₁ : S₁ → Distribution.ProbDist S₂} (K₂ : T₁ → Distribution.ProbDist T₂) {a : S₁} {i : I}
    {x : X₁ i} (hf : SimulatesAt f₁ f₂ K₁ a ⟨i, x⟩) (b : T₁) :
    SimulatesAt (ProbStep.parallel f₁ g₁) (ProbStep.parallel f₂ g₂) (prodKernel K₁ K₂) (a, b)
      ⟨.inl i, x⟩ := by
  unfold SimulatesAt at hf ⊢
  calc bindK (prodKernel K₁ K₂ (a, b)).1
        (fun s₂ => (ProbStep.parallel f₂ g₂).outcome s₂ ⟨.inl i, x⟩)
      = bindK (K₁ a).1 fun a₂ => bindK (K₂ b).1 fun b₂ =>
          fTransform (fun p => ((p.1, b₂), inlReply p.2)) (f₂.outcome a₂ ⟨i, x⟩) := by
        simp only [prodKernel, bindK_bindK, bindK_fTransform, Function.comp_def,
          outcome_parallel_inl]
    _ = bindK (K₂ b).1 fun b₂ => fTransform (fun p => ((p.1, b₂), inlReply p.2))
          (bindK (K₁ a).1 fun a₂ => f₂.outcome a₂ ⟨i, x⟩) := by
        rw [bindK_comm]
        simp only [fTransform_bindK]
    _ = bindK (K₂ b).1 fun b₂ => bindK (f₁.outcome a ⟨i, x⟩) fun p =>
          fTransform (fun a₂ => ((a₂, b₂), inlReply p.2)) (K₁ p.1).1 := by
        rw [hf]
        simp only [fTransform_bindK, fTransform_fTransform, Function.comp_def]
    _ = bindK (f₁.outcome a ⟨i, x⟩) fun p => bindK (K₁ p.1).1 fun a₂ =>
          fTransform (fun b₂ => ((a₂, b₂), inlReply p.2)) (K₂ b).1 := by
        rw [bindK_comm]
        exact bindK_congr fun p _ => bindK_fTransform_pair_comm _ _ _
    _ = _ := by
        rw [outcome_parallel_inl, bindK_fTransform]
        refine bindK_congr fun p _ => ?_
        simp only [Function.comp_def, prodKernel, fTransform_bindK, fTransform_fTransform]

/-- **A simulation step side by side, at the right automaton.** -/
lemma simulatesAt_parallel_inr {S₁ T₁ S₂ T₂ : Type} (f₁ : ProbStep S₁ I X₁ Y₁)
    (f₂ : ProbStep S₂ I X₁ Y₁) {g₁ : ProbStep T₁ J X₂ Y₂} {g₂ : ProbStep T₂ J X₂ Y₂}
    (K₁ : S₁ → Distribution.ProbDist S₂) {K₂ : T₁ → Distribution.ProbDist T₂} {b : T₁} {j : J}
    {x : X₂ j} (hg : SimulatesAt g₁ g₂ K₂ b ⟨j, x⟩) (a : S₁) :
    SimulatesAt (ProbStep.parallel f₁ g₁) (ProbStep.parallel f₂ g₂) (prodKernel K₁ K₂) (a, b)
      ⟨.inr j, x⟩ := by
  unfold SimulatesAt at hg ⊢
  calc bindK (prodKernel K₁ K₂ (a, b)).1
        (fun s₂ => (ProbStep.parallel f₂ g₂).outcome s₂ ⟨.inr j, x⟩)
      = bindK (K₁ a).1 fun a₂ => bindK (K₂ b).1 fun b₂ =>
          fTransform (fun p => ((a₂, p.1), inrReply p.2)) (g₂.outcome b₂ ⟨j, x⟩) := by
        simp only [prodKernel, bindK_bindK, bindK_fTransform, Function.comp_def,
          outcome_parallel_inr]
    _ = bindK (K₁ a).1 fun a₂ => fTransform (fun p => ((a₂, p.1), inrReply p.2))
          (bindK (K₂ b).1 fun b₂ => g₂.outcome b₂ ⟨j, x⟩) := by
        simp only [fTransform_bindK]
    _ = bindK (K₁ a).1 fun a₂ => bindK (g₁.outcome b ⟨j, x⟩) fun p =>
          fTransform (fun b₂ => ((a₂, b₂), inrReply p.2)) (K₂ p.1).1 := by
        rw [hg]
        simp only [fTransform_bindK, fTransform_fTransform, Function.comp_def]
    _ = bindK (g₁.outcome b ⟨j, x⟩) fun p => bindK (K₁ a).1 fun a₂ =>
          fTransform (fun b₂ => ((a₂, b₂), inrReply p.2)) (K₂ p.1).1 := by
        rw [bindK_comm]
    _ = _ := by
        rw [outcome_parallel_inr, bindK_fTransform]
        refine bindK_congr fun p _ => ?_
        simp only [Function.comp_def, prodKernel, fTransform_bindK, fTransform_fTransform]


end Parallel

end ProbStep

namespace Program

variable {S O J R : Type} {U V : O → Type} {X Y : J → Type} (P : Program S O J U V X Y)
  (stepR : ProbStep R J X Y)

/-- **An invocation against a probabilistic automaton**: the body runs from the exchanges `h`,
the automaton in the state `r` answering its inside queries, with at most `n` more of them; the
law of the next states and of the reply. -/
noncomputable def probInvoke (s : S) (o : O) (u : U o) :
    ℕ → R → List ((Σ j, X j) × (Σ j, Y j)) → Distribution ((S × R) × V o)
  | 0, r, h => match P s o u h with
    | .inl a => Finsupp.single ((a.1, r), a.2) 1
    | .inr _ => 0
  | n + 1, r, h => match P s o u h with
    | .inl a => Finsupp.single ((a.1, r), a.2) 1
    | .inr q => bindK (stepR.outcome r q) fun p => probInvoke s o u n p.1 (h ++ [(q, p.2)])

variable {P stepR}

lemma probInvoke_inl {s : S} {o : O} {u : U o} {h : List ((Σ j, X j) × (Σ j, Y j))}
    {a : S × V o} (ha : P s o u h = .inl a) (n : ℕ) (r : R) :
    P.probInvoke stepR s o u n r h = Finsupp.single ((a.1, r), a.2) 1 := by
  cases n <;> simp [probInvoke, ha]

lemma probInvoke_zero_inr {s : S} {o : O} {u : U o} {h : List ((Σ j, X j) × (Σ j, Y j))}
    {q : Σ j, X j} (hq : P s o u h = .inr q) (r : R) :
    P.probInvoke stepR s o u 0 r h = 0 := by
  simp [probInvoke, hq]

lemma probInvoke_succ_inr {s : S} {o : O} {u : U o} {h : List ((Σ j, X j) × (Σ j, Y j))}
    {q : Σ j, X j} (hq : P s o u h = .inr q) (n : ℕ) (r : R) :
    P.probInvoke stepR s o u (n + 1) r h =
      bindK (stepR.outcome r q) fun p => P.probInvoke stepR s o u n p.1 (h ++ [(q, p.2)]) := by
  simp [probInvoke, hq]

lemma probInvoke_nonNeg (s : S) (o : O) (u : U o) :
    ∀ n r h, (P.probInvoke stepR s o u n r h).NonNeg := by
  intro n
  induction n with
  | zero =>
    intro r h
    cases hq : P s o u h with
    | inl a => rw [probInvoke_inl hq]; exact (isProbDist_single _).1
    | inr q => rw [probInvoke_zero_inr hq]; exact fun _ => le_rfl
  | succ n ih =>
    intro r h
    cases hq : P s o u h with
    | inl a => rw [probInvoke_inl hq]; exact (isProbDist_single _).1
    | inr q =>
      rw [probInvoke_succ_inr hq]
      exact bindK_nonNeg (stepR.outcome_nonNeg r q) fun _ => ih _ _

/-- The replies of an outcome are at the queried label. -/
lemma mem_support_outcome {r : R} {q : Σ j, X j} {p : R × Σ j, Y j}
    (hp : p ∈ (stepR.outcome r q).support) : ∃ y : Y q.1, p.2 = ⟨q.1, y⟩ := by
  classical
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp (support_fTransform_subset _ _ hp)
  exact ⟨a.2, rfl⟩

/-- A bounded program completes each invocation against a probabilistic automaton. -/
lemma probInvoke_weight {b : ℕ} (hP : P.Bounded b) (s : S) (o : O) (u : U o) :
    ∀ n r h, P.Consistent s o u h → b ≤ n + h.length →
      (P.probInvoke stepR s o u n r h).weight = 1 := by
  intro n
  induction n with
  | zero =>
    intro r h hc hb
    cases hq : P s o u h with
    | inl a => rw [probInvoke_inl hq]; exact (isProbDist_single _).2
    | inr q => exact absurd (hP s o u h q hc hq) (by omega)
  | succ n ih =>
    intro r h hc hb
    cases hq : P s o u h with
    | inl a => rw [probInvoke_inl hq]; exact (isProbDist_single _).2
    | inr q =>
      rw [probInvoke_succ_inr hq, weight_bindK_of_weight fun p hp => ?_, stepR.weight_outcome]
      obtain ⟨y, hy⟩ := mem_support_outcome hp
      rw [hy]
      exact ih _ _ (hc.snoc hq y) (by simp; omega)

variable (P stepR) in
/-- **The program attached to a probabilistic automaton**, a probabilistic automaton on pairs of
states: each input runs an invocation, the automaton answering its inside queries. -/
noncomputable def probCombine {b : ℕ} (hP : P.Bounded b) : ProbStep (S × R) O U V :=
  fun sr o u => ⟨P.probInvoke stepR sr.1 o u b sr.2 [],
    probInvoke_nonNeg sr.1 o u b sr.2 [],
    probInvoke_weight hP sr.1 o u b sr.2 [] (consistent_nil P _ _ _) (by simp)⟩

lemma probCombine_val {b : ℕ} (hP : P.Bounded b) (sr : S × R) (o : O) (u : U o) :
    (P.probCombine stepR hP sr o u).1 = P.probInvoke stepR sr.1 o u b sr.2 [] := rfl

/-- Against a deterministic automaton, an invocation is the point law of its completion. -/
lemma probInvoke_ofDeterministic (stepD : R → (j : J) → X j → R × Y j) (s : S) (o : O)
    (u : U o) : ∀ n r h v, P.invoke stepD s o u n r h = some v →
      P.probInvoke (ProbStep.ofDeterministic stepD) s o u n r h = Finsupp.single v 1 := by
  intro n
  induction n with
  | zero =>
    intro r h v hv
    cases hq : P s o u h with
    | inl a =>
      simp only [invoke, hq, Sum.elim_inl, Option.some.injEq] at hv
      rw [probInvoke_inl hq, hv]
    | inr q => simp [invoke, hq] at hv
  | succ n ih =>
    intro r h v hv
    cases hq : P s o u h with
    | inl a =>
      simp only [invoke, hq, Option.some.injEq] at hv
      rw [probInvoke_inl hq, ← hv]
    | inr q =>
      simp only [invoke, hq] at hv
      rw [probInvoke_succ_inr hq, ProbStep.outcome_ofDeterministic, bindK_single, one_smul]
      exact ih _ _ v hv

/-- **A program attached to a deterministic automaton** is the point law of the combined
automaton. -/
lemma ofDeterministic_combine (stepD : R → (j : J) → X j → R × Y j) {b : ℕ}
    (hP : P.Bounded b) :
    ProbStep.ofDeterministic (P.combine stepD hP) =
      P.probCombine (ProbStep.ofDeterministic stepD) hP := by
  funext sr o u
  apply Subtype.ext
  exact (probInvoke_ofDeterministic stepD sr.1 o u b sr.2 [] _
    (invoke_eq_combine stepD hP sr o u)).symm

/-- A label with inputs in a list is the label of one of its entries. -/
lemma _root_.SystemAlgebra.exists_mem_of_restrict_ne_nil {K : Type} {A : K → Type} {k : K}
    {l : List (Σ k, A k)} (h : SystemAlgebra.restrict k l ≠ []) : ∃ x ∈ l, x.1 = k := by
  induction l with
  | nil => exact absurd rfl h
  | cons x l ih =>
    obtain ⟨k', a⟩ := x
    by_cases hk : k' = k
    · exact ⟨⟨k', a⟩, List.mem_cons_self, hk⟩
    · rw [SystemAlgebra.restrict_cons_ne hk] at h
      obtain ⟨y, hy, hyk⟩ := ih h
      exact ⟨y, List.mem_cons_of_mem _ hy, hyk⟩

section Simulation

variable {R₁ R₂ : Type} {stepR₁ : ProbStep R₁ J X Y} {stepR₂ : ProbStep R₂ J X Y}
  {K : R₁ → Distribution.ProbDist R₂} {E : List (Σ j, X j) → Prop}
  {invR : List (Σ j, X j) → R₁ → Prop}

variable (P) in
/-- After the inside queries `τ`, every inside query of an invocation at `⟨o, u⟩` in the state `s`
is admitted by `E`. -/
def AdmitsInvocation (E : List (Σ j, X j) → Prop) (s : S) (o : O) (u : U o)
    (τ : List (Σ j, X j)) : Prop :=
  ∀ h q, P.Consistent s o u h → P s o u h = .inr q → E (τ ++ h.map Prod.fst ++ [q])

/-- **An invocation along simulation steps** of the inside automata: from the kernel image of `r`,
the invocation against `stepR₂` is the invocation against `stepR₁` followed by the kernel. -/
lemma probInvoke_simulation
    (hsim : ∀ τ r q, invR τ r → E (τ ++ [q]) → ProbStep.SimulatesAt stepR₁ stepR₂ K r q)
    (hpres : ∀ τ r q, invR τ r → E (τ ++ [q]) →
      ∀ p ∈ (stepR₁.outcome r q).support, invR (τ ++ [q]) p.1)
    (s : S) (o : O) (u : U o) (τ : List (Σ j, X j)) (hgood : P.AdmitsInvocation E s o u τ) :
    ∀ n r h, P.Consistent s o u h → invR (τ ++ h.map Prod.fst) r →
      (bindK (K r).1 fun r₂ => P.probInvoke stepR₂ s o u n r₂ h) =
        bindK (P.probInvoke stepR₁ s o u n r h) fun p =>
          fTransform (fun r₂ => ((p.1.1, r₂), p.2)) (K p.1.2).1 := by
  intro n
  induction n with
  | zero =>
    intro r h _ _
    cases hq : P s o u h with
    | inl a =>
      simp only [probInvoke_inl hq, bindK_single, one_smul]
      exact bindK_single_comp _ _
    | inr q => simp only [probInvoke_zero_inr hq, bindK_zero, bindK_zero_right]
  | succ n ih =>
    intro r h hc hr
    cases hq : P s o u h with
    | inl a =>
      simp only [probInvoke_inl hq, bindK_single, one_smul]
      exact bindK_single_comp _ _
    | inr q =>
      have hE := hgood h q hc hq
      have hs := hsim _ r q hr hE
      unfold ProbStep.SimulatesAt at hs
      simp only [probInvoke_succ_inr hq]
      calc (bindK (K r).1 fun r₂ => bindK (stepR₂.outcome r₂ q) fun p =>
            P.probInvoke stepR₂ s o u n p.1 (h ++ [(q, p.2)]))
          = bindK (bindK (K r).1 fun r₂ => stepR₂.outcome r₂ q) fun p =>
              P.probInvoke stepR₂ s o u n p.1 (h ++ [(q, p.2)]) := (bindK_bindK _ _ _).symm
        _ = bindK (stepR₁.outcome r q) fun p => bindK (K p.1).1 fun r₂ =>
              P.probInvoke stepR₂ s o u n r₂ (h ++ [(q, p.2)]) := by
            rw [hs, bindK_bindK]
            refine bindK_congr fun p _ => ?_
            rw [bindK_fTransform]
            rfl
        _ = bindK (stepR₁.outcome r q) fun p =>
              bindK (P.probInvoke stepR₁ s o u n p.1 (h ++ [(q, p.2)])) fun p' =>
                fTransform (fun r₂ => ((p'.1.1, r₂), p'.2)) (K p'.1.2).1 :=
            bindK_congr fun p hp => by
              obtain ⟨y, hy⟩ := mem_support_outcome hp
              refine ih _ _ (hy ▸ hc.snoc hq y) ?_
              have := hpres _ r q hr hE p hp
              simpa using this
        _ = _ := (bindK_bindK _ _ _).symm

/-- **The end of an invocation**: each outcome of an invocation is the reply of the body on
consistent exchanges extending `h`, with the invariant on the inside queries made. -/
lemma probInvoke_support
    (hpres : ∀ τ r q, invR τ r → E (τ ++ [q]) →
      ∀ p ∈ (stepR₁.outcome r q).support, invR (τ ++ [q]) p.1)
    (s : S) (o : O) (u : U o) (τ : List (Σ j, X j)) (hgood : P.AdmitsInvocation E s o u τ) :
    ∀ n r h, P.Consistent s o u h → invR (τ ++ h.map Prod.fst) r →
      ∀ p ∈ (P.probInvoke stepR₁ s o u n r h).support, ∃ hf, P.Consistent s o u hf ∧
        h <+: hf ∧ P s o u hf = .inl (p.1.1, p.2) ∧ invR (τ ++ hf.map Prod.fst) p.1.2 := by
  intro n
  induction n with
  | zero =>
    intro r h hc hr p hp
    cases hq : P s o u h with
    | inl a =>
      rw [probInvoke_inl hq, Finsupp.mem_support_single] at hp
      rw [hp.1]
      exact ⟨h, hc, List.prefix_refl _, hq, hr⟩
    | inr q => rw [probInvoke_zero_inr hq] at hp; simp at hp
  | succ n ih =>
    intro r h hc hr p hp
    cases hq : P s o u h with
    | inl a =>
      rw [probInvoke_inl hq, Finsupp.mem_support_single] at hp
      rw [hp.1]
      exact ⟨h, hc, List.prefix_refl _, hq, hr⟩
    | inr q =>
      rw [probInvoke_succ_inr hq] at hp
      obtain ⟨p', hp', hp⟩ := mem_support_bindK hp
      obtain ⟨y, hy⟩ := mem_support_outcome hp'
      have hr' : invR (τ ++ (h ++ [(q, p'.2)]).map Prod.fst) p'.1 := by
        simpa using hpres _ r q hr (hgood h q hc hq) p' hp'
      obtain ⟨hf, hcf, hpf, hf₁, hf₂⟩ := ih _ _ (hy ▸ hc.snoc hq y) hr' p hp
      exact ⟨hf, hcf, (List.prefix_append h _).trans hpf, hf₁, hf₂⟩

/-- The kernel on the inside state, the program state unchanged. -/
noncomputable def insideKernel (K : R₁ → Distribution.ProbDist R₂) (sr : S × R₁) :
    Distribution.ProbDist (S × R₂) :=
  ⟨fTransform (fun r₂ => (sr.1, r₂)) (K sr.2).1, (K sr.2).2.1.fTransform _, by
    rw [weight_fTransform]; exact (K sr.2).2.2⟩

variable (P) in
/-- **A program along simulation steps** of the inside automata: when the inside queries of the
invocation are admitted and simulated, the program on `stepR₂` simulates the program on `stepR₁`
along the kernel on the inside state. -/
lemma simulatesAt_probCombine {b : ℕ} (hP : P.Bounded b)
    (hsim : ∀ τ r q, invR τ r → E (τ ++ [q]) → ProbStep.SimulatesAt stepR₁ stepR₂ K r q)
    (hpres : ∀ τ r q, invR τ r → E (τ ++ [q]) →
      ∀ p ∈ (stepR₁.outcome r q).support, invR (τ ++ [q]) p.1)
    {s : S} {r : R₁} {τ : List (Σ j, X j)} (hr : invR τ r) {x : Σ o, U o}
    (hgood : P.AdmitsInvocation E s x.1 x.2 τ) :
    ProbStep.SimulatesAt (P.probCombine stepR₁ hP) (P.probCombine stepR₂ hP) (insideKernel K)
      (s, r) x := by
  obtain ⟨o, u⟩ := x
  have hinv := probInvoke_simulation (P := P) hsim hpres s o u τ hgood b r []
    (consistent_nil P _ _ _) (by simpa using hr)
  unfold ProbStep.SimulatesAt
  simp only [insideKernel, ProbStep.outcome, probCombine_val, bindK_fTransform, Function.comp_def]
  rw [← fTransform_bindK, hinv, fTransform_bindK]
  refine bindK_congr fun p _ => ?_
  simp only [fTransform_fTransform, Function.comp_def]
  rfl

variable (P) in
/-- The outcomes of the program attached to `stepR₁` come from consistent exchanges of the body,
with the invariant on the inside queries made. -/
lemma probCombine_support {b : ℕ} (hP : P.Bounded b)
    (hpres : ∀ τ r q, invR τ r → E (τ ++ [q]) →
      ∀ p ∈ (stepR₁.outcome r q).support, invR (τ ++ [q]) p.1)
    {s : S} {r : R₁} {τ : List (Σ j, X j)} (hr : invR τ r) {x : Σ o, U o}
    (hgood : P.AdmitsInvocation E s x.1 x.2 τ) :
    ∀ p ∈ ((P.probCombine stepR₁ hP).outcome (s, r) x).support, ∃ hf,
      P.Consistent s x.1 x.2 hf ∧ invR (τ ++ hf.map Prod.fst) p.1.2 := by
  intro p hp
  obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp (support_fTransform_subset _ _ hp)
  obtain ⟨hf, hcf, -, -, hinv⟩ := probInvoke_support (P := P) hpres s x.1 x.2 τ hgood b r []
    (consistent_nil P _ _ _) (by simpa using hr) p' hp'
  exact ⟨hf, hcf, hinv⟩

variable (P) in
/-- A consistent exchange list is the consistent list before its last entry, whose query the
body made there. -/
lemma Consistent.of_snoc {s : S} {o : O} {u : U o} {h : List ((Σ j, X j) × (Σ j, Y j))}
    {e : (Σ j, X j) × (Σ j, Y j)} (hc : P.Consistent s o u (h ++ [e])) :
    P.Consistent s o u h ∧ P s o u h = .inr e.1 := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have := hc i (by simp; omega)
    rwa [List.take_append_of_le_length hi.le, List.getElem_append_left hi] at this
  · have := (hc h.length (by simp)).1
    rw [List.take_left' rfl, List.getElem_append_right (le_refl _)] at this
    simpa using this

variable (P) in
/-- **Port preservation counts, one query further**: if the labels `ι o'` are queried at most once
along consistent exchanges of an invocation at `o`, and only when `o' = o`, so they are with the
next query. -/
lemma PreservesAt.restrict_length_le_step {ι : O → Option J} {s : S} {o : O} {u : U o}
    (hι : PreservesAt ι o (P s o u)) {h : List ((Σ j, X j) × (Σ j, Y j))}
    (hc : P.Consistent s o u h) {q₀ : Σ j, X j} (hq : P s o u h = .inr q₀)
    (ih : ∀ o' j, ι o' = some j → SystemAlgebra.restrict j (h.map Prod.fst) = [] ∨
      (o' = o ∧ (SystemAlgebra.restrict j (h.map Prod.fst)).length = 1))
    (o' : O) (j : J) (hj : ι o' = some j) :
    SystemAlgebra.restrict j (h.map Prod.fst ++ [q₀]) = [] ∨
      (o' = o ∧ (SystemAlgebra.restrict j (h.map Prod.fst ++ [q₀])).length = 1) := by
  obtain ⟨k, v⟩ := q₀
  rw [SystemAlgebra.restrict_append]
  by_cases hk : k = j
  · subst hk
    obtain ⟨ho, hnone⟩ := hι h ⟨k, v⟩ hc hq o' hj
    have hnil : SystemAlgebra.restrict k (h.map Prod.fst) = [] := by
      by_contra hne
      obtain ⟨w, hw, hwk⟩ := SystemAlgebra.exists_mem_of_restrict_ne_nil hne
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hw
      exact hnone e' he' hwk
    right
    simp [hnil, ho]
  · rw [SystemAlgebra.restrict_cons_ne hk, SystemAlgebra.restrict_nil, List.append_nil]
    exact ih o' j hj

variable (P) in
/-- **Port preservation counts**: along consistent exchanges of an invocation at `o`, a label
`ι o'` is queried at most once, and only when `o' = o`. -/
lemma PreservesAt.restrict_length_le {ι : O → Option J} {s : S} {o : O} {u : U o}
    (hι : PreservesAt ι o (P s o u)) {h : List ((Σ j, X j) × (Σ j, Y j))}
    (hc : P.Consistent s o u h) (o' : O) (j : J) (hj : ι o' = some j) :
    SystemAlgebra.restrict j (h.map Prod.fst) = [] ∨
      (o' = o ∧ (SystemAlgebra.restrict j (h.map Prod.fst)).length = 1) := by
  induction h using List.reverseRecOn generalizing o' j with
  | nil => exact Or.inl rfl
  | append_singleton h e ih =>
    obtain ⟨hc', hq⟩ := Consistent.of_snoc P hc
    rw [List.map_append, List.map_singleton]
    exact PreservesAt.restrict_length_le_step P hι hc' hq
      (fun o'' j' hj' => ih hc' o'' j' hj') o' j hj

variable (P) in
/-- **Port preservation counts with the next query.** -/
lemma PreservesAt.restrict_length_le_snoc {ι : O → Option J} {s : S} {o : O} {u : U o}
    (hι : PreservesAt ι o (P s o u)) {h : List ((Σ j, X j) × (Σ j, Y j))}
    (hc : P.Consistent s o u h) {q₀ : Σ j, X j} (hq : P s o u h = .inr q₀) (o' : O) (j : J)
    (hj : ι o' = some j) :
    SystemAlgebra.restrict j (h.map Prod.fst ++ [q₀]) = [] ∨
      (o' = o ∧ (SystemAlgebra.restrict j (h.map Prod.fst ++ [q₀])).length = 1) :=
  PreservesAt.restrict_length_le_step P hι hc hq
    (fun o'' j' hj' => PreservesAt.restrict_length_le P hι hc o'' j' hj') o' j hj

variable (P) in
/-- **Per-label counts with the next query**: along consistent exchanges of a body with a per-label
call bound `n`, each label `j` is queried at most `n j` times, also with the next query. -/
lemma LabelCallBound.restrict_length_le_snoc {n : J → ℕ} {s : S} {o : O} {u : U o}
    (hn : LabelCallBound n (P s o u)) :
    ∀ {h : List ((Σ j, X j) × (Σ j, Y j))}, P.Consistent s o u h → ∀ {q₀ : Σ j, X j},
      P s o u h = .inr q₀ → ∀ j, (SystemAlgebra.restrict j (h.map Prod.fst ++ [q₀])).length ≤ n j
  := by
  intro h
  induction h using List.reverseRecOn with
  | nil =>
    intro _ q₀ hq j
    have := hn [] q₀ (consistent_nil P _ _ _) hq
    obtain ⟨k, v⟩ := q₀
    by_cases hk : k = j
    · subst hk
      simp at this ⊢
      omega
    · simp [SystemAlgebra.restrict_cons_ne hk]
  | append_singleton h e ih =>
    intro hc q₀ hq j
    obtain ⟨hc', he⟩ := Consistent.of_snoc P hc
    have hprev := ih hc' he
    have hnext := hn _ q₀ hc hq
    rw [List.map_append, List.map_singleton] at hnext ⊢
    obtain ⟨k, v⟩ := q₀
    rw [SystemAlgebra.restrict_append]
    by_cases hk : k = j
    · subst hk
      simp only [SystemAlgebra.restrict_cons_self, SystemAlgebra.restrict_nil, List.length_append,
        List.length_singleton]
      exact hnext
    · rw [SystemAlgebra.restrict_cons_ne hk, SystemAlgebra.restrict_nil, List.append_nil]
      exact hprev j

variable (P) in
/-- **Per-label counts**: along consistent exchanges of a body with a per-label call bound `n`,
each label `j` is queried at most `n j` times. -/
lemma LabelCallBound.restrict_length_le {n : J → ℕ} {s : S} {o : O} {u : U o}
    (hn : LabelCallBound n (P s o u)) {h : List ((Σ j, X j) × (Σ j, Y j))}
    (hc : P.Consistent s o u h) (j : J) :
    (SystemAlgebra.restrict j (h.map Prod.fst)).length ≤ n j := by
  rcases List.eq_nil_or_concat h with rfl | ⟨h', e, rfl⟩
  · exact Nat.zero_le _
  · rw [List.concat_eq_append] at hc ⊢
    obtain ⟨hc', he⟩ := Consistent.of_snoc P hc
    rw [List.map_append, List.map_singleton]
    exact LabelCallBound.restrict_length_le_snoc P hn hc' he j

end Simulation


end Program

namespace ProbStep

variable {Z : Type}

/-- **Fresh samples**: each query of a source answers an independent sample of `law`. -/
noncomputable def fresh (law : Distribution.ProbDist Z) :
    ProbStep Unit Unit (fun _ => Unit) (fun _ => Z) :=
  fun _ _ _ => ⟨fTransform (fun z => ((), z)) law.1, fTransform_isProbDist _ law.2⟩

/-- Fresh samples, remembering the samples read so far. -/
noncomputable def readFresh (law : Distribution.ProbDist Z) :
    ProbStep (List Z) Unit (fun _ => Unit) (fun _ => Z) :=
  fun r _ _ => ⟨fTransform (fun z => (r ++ [z], z)) law.1, fTransform_isProbDist _ law.2⟩

/-- The entries of a source table after the reads `r`: the reads, then independent samples. -/
noncomputable def tableEntries (law : Distribution.ProbDist Z) {q : ℕ} (r : List Z) :
    Fin q → Distribution Z :=
  fun j => if h : j.val < r.length then Finsupp.single r[j.val] 1 else law.1

/-- **The table of a source after the reads `r`**, with its counter at the number of reads. -/
noncomputable def tableKernel (law : Distribution.ProbDist Z) (q : ℕ) (r : List Z) :
    Distribution.ProbDist ((Fin q → Z) × ℕ) :=
  ⟨fTransform (fun t => (t, r.length)) (pi (tableEntries law r)),
    fTransform_isProbDist _ (pi_isProbDist fun j => by
      unfold tableEntries
      split_ifs
      · exact isProbDist_single _
      · exact law.2)⟩

lemma tableKernel_nil (law : Distribution.ProbDist Z) (q : ℕ) :
    (tableKernel law q []).1 = fTransform (fun t => (t, 0)) (pi fun _ : Fin q => law.1) := by
  change fTransform _ (pi (tableEntries law [])) = _
  congr 2

lemma tableEntries_update (law : Distribution.ProbDist Z) {q : ℕ} (r : List Z) (z : Z)
    (hr : r.length < q) :
    Function.update (tableEntries (q := q) law r) ⟨r.length, hr⟩ (Finsupp.single z 1) =
      tableEntries law (r ++ [z]) := by
  funext j
  by_cases hj : j = ⟨r.length, hr⟩
  · subst hj
    simp [tableEntries]
  · rw [Function.update_of_ne hj]
    have hj' : j.val ≠ r.length := fun h => hj (Fin.ext h)
    unfold tableEntries
    by_cases hlt : j.val < r.length
    · rw [dif_pos hlt, dif_pos (by simp; omega), List.getElem_append_left hlt]
    · rw [dif_neg hlt, dif_neg (by simp; omega)]

omit [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] in
omit [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] in
/-- **A source table read in order is fresh sampling**: the source on the table after the reads
`r` simulates fresh samples remembering their reads, while fewer than `q` entries are read. -/
lemma simulatesAt_source [Fintype Z] (law : Distribution.ProbDist Z) (q : ℕ) (r : List Z)
    (hq : r.length < q) (x : Σ _ : Unit, Unit) :
    SimulatesAt (readFresh law) (ofDeterministic (Interface.sourceStep (q := q) law))
      (tableKernel law q) r x := by
  obtain ⟨⟨⟩, ⟨⟩⟩ := x
  have hentry : tableEntries (q := q) law r ⟨r.length, hq⟩ = law.1 := by
    simp [tableEntries]
  unfold SimulatesAt
  calc bindK (tableKernel law q r).1
        (fun tn => (ofDeterministic (Interface.sourceStep (q := q) law)).outcome tn ⟨(), ()⟩)
      = fTransform (fun t => ((t, r.length + 1), (⟨(), t ⟨r.length, hq⟩⟩ : Σ _ : Unit, Z)))
          (pi (tableEntries law r)) := by
        simp only [tableKernel, bindK_fTransform, Function.comp_def, outcome_ofDeterministic]
        rw [← bindK_single_comp]
        refine bindK_congr fun t _ => ?_
        simp [Interface.sourceStep, hq]
    _ = bindK law.1 fun z => fTransform (fun t => ((t, r.length + 1), (⟨(), z⟩ : Σ _ : Unit, Z)))
          (pi (tableEntries law (r ++ [z]))) := by
        rw [pi_eq_bindK_update _ ⟨r.length, hq⟩, fTransform_bindK, hentry]
        refine bindK_congr fun z _ => ?_
        rw [tableEntries_update law r z hq]
        refine fTransform_congr_support fun t ht => ?_
        rw [← tableEntries_update law r z hq] at ht
        rw [eq_of_mem_support_pi_update _ _ z ht]
    _ = _ := by
        simp only [ProbStep.outcome, readFresh, tableKernel, bindK_fTransform, Function.comp_def,
          fTransform_fTransform, tagged]
        refine bindK_congr fun z _ => ?_
        simp

omit [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] in
/-- Forgetting the reads of fresh samples. -/
lemma simulatesAt_forgetReads (law : Distribution.ProbDist Z) (r : List Z)
    (x : Σ _ : Unit, Unit) :
    SimulatesAt (readFresh law) (fresh law) (fun _ => Distribution.ProbDist.single ()) r x := by
  obtain ⟨⟨⟩, ⟨⟩⟩ := x
  unfold SimulatesAt
  simp only [Distribution.ProbDist.single, bindK_single, one_smul, ProbStep.outcome, readFresh,
    fresh, bindK_fTransform, Function.comp_def, fTransform_fTransform]
  rw [fTransform_eq_bindK]
  refine bindK_congr fun z _ => ?_
  simp [fTransform, tagged]

end ProbStep


/-- **A simulation on a domain**: a kernel and an invariant of the inputs so far, preserved by
`step₁`, along which `step₂` simulates `step₁` at every query the domain `E` admits. -/
structure SimulationOn {S₁ S₂ I : Type} {X Y : I → Type} (E : List (Σ i, X i) → Prop)
    (step₁ : ProbStep S₁ I X Y) (step₂ : ProbStep S₂ I X Y) where
  /-- The kernel from the states of `step₁` to those of `step₂`. -/
  kernel : S₁ → Distribution.ProbDist S₂
  /-- The states of `step₁` after the inputs `xs`. -/
  inv : List (Σ i, X i) → S₁ → Prop
  pres : ∀ xs s x, inv xs s → E (xs ++ [x]) →
    ∀ p ∈ (step₁.outcome s x).support, inv (xs ++ [x]) p.1
  sim : ∀ xs s x, inv xs s → E (xs ++ [x]) → ProbStep.SimulatesAt step₁ step₂ kernel s x

/-- **Equal resources along a simulation on the domain of the interface.** -/
lemma Interface.Resource.ofProbAutomaton_eq_of_simulationOn {T : Interface} {S₁ S₂ : Type}
    {step₁ : ProbStep S₁ T.I T.X T.Y} {step₂ : ProbStep S₂ T.I T.X T.Y}
    (σ : SimulationOn T.domain step₁ step₂) (init₁ : Distribution.ProbDist S₁)
    (init₂ : Distribution.ProbDist S₂) (hinit : ∀ s ∈ init₁.1.support, σ.inv [] s)
    (hK : init₂.1 = bindK init₁.1 fun s => (σ.kernel s).1) :
    Interface.Resource.ofProbAutomaton T step₁ init₁ =
      Interface.Resource.ofProbAutomaton T step₂ init₂ :=
  Interface.Resource.ofProbAutomaton_eq_of_simulation step₁ step₂ init₁ init₂ σ.kernel σ.inv
    hinit σ.pres σ.sim hK

namespace Interface

variable {A B : Interface}

/-- The inputs of a history of the parallel interface at the left interface. -/
noncomputable def leftInputs (xs : List (Σ l, (Interface.tensor A B).X l)) : List (Σ i, A.X i) :=
  SystemAlgebra.restrict none (xs.map (sumAlphabet (Sum.rec A.X B.X)).symm)

/-- The inputs of a history of the parallel interface at the right interface. -/
noncomputable def rightInputs (xs : List (Σ l, (Interface.tensor A B).X l)) : List (Σ j, B.X j) :=
  SystemAlgebra.restrict (some ()) (xs.map (sumAlphabet (Sum.rec A.X B.X)).symm)

lemma leftInputs_inl (xs : List (Σ l, (Interface.tensor A B).X l)) (i : A.I) (x : A.X i) :
    leftInputs (xs ++ [⟨.inl i, x⟩]) = leftInputs xs ++ [⟨i, x⟩] := by
  simp only [leftInputs, List.map_append, List.map_singleton, SystemAlgebra.restrict_append]
  congr 1
  change SystemAlgebra.restrict none [(⟨none, ⟨i, x⟩⟩ : Two (Σ i, A.X i) (Σ j, B.X j))] = _
  simp

lemma leftInputs_inr (xs : List (Σ l, (Interface.tensor A B).X l)) (j : B.I) (y : B.X j) :
    leftInputs (xs ++ [⟨.inr j, y⟩]) = leftInputs xs := by
  simp only [leftInputs, List.map_append, List.map_singleton, SystemAlgebra.restrict_append]
  change _ ++ SystemAlgebra.restrict none [(⟨some (), ⟨j, y⟩⟩ : Two (Σ i, A.X i) (Σ j, B.X j))] = _
  rw [SystemAlgebra.restrict_cons_ne (by simp)]
  simp

lemma rightInputs_inl (xs : List (Σ l, (Interface.tensor A B).X l)) (i : A.I) (x : A.X i) :
    rightInputs (xs ++ [⟨.inl i, x⟩]) = rightInputs xs := by
  simp only [rightInputs, List.map_append, List.map_singleton, SystemAlgebra.restrict_append]
  change _ ++ SystemAlgebra.restrict (some ())
    [(⟨none, ⟨i, x⟩⟩ : Two (Σ i, A.X i) (Σ j, B.X j))] = _
  rw [SystemAlgebra.restrict_cons_ne (by simp)]
  simp

lemma rightInputs_inr (xs : List (Σ l, (Interface.tensor A B).X l)) (j : B.I) (y : B.X j) :
    rightInputs (xs ++ [⟨.inr j, y⟩]) = rightInputs xs ++ [⟨j, y⟩] := by
  simp only [rightInputs, List.map_append, List.map_singleton, SystemAlgebra.restrict_append]
  congr 1
  change SystemAlgebra.restrict (some ()) [(⟨some (), ⟨j, y⟩⟩ : Two (Σ i, A.X i) (Σ j, B.X j))] = _
  simp

lemma tensor_domain_inl {xs : List (Σ l, (Interface.tensor A B).X l)} {i : A.I} {x : A.X i}
    (h : (Interface.tensor A B).domain (xs ++ [⟨.inl i, x⟩])) :
    A.domain (leftInputs xs ++ [⟨i, x⟩]) := by
  have := h.2.1
  rw [← leftInputs, leftInputs_inl] at this
  exact this.resolve_left (by simp)

lemma tensor_domain_inr {xs : List (Σ l, (Interface.tensor A B).X l)} {j : B.I} {y : B.X j}
    (h : (Interface.tensor A B).domain (xs ++ [⟨.inr j, y⟩])) :
    B.domain (rightInputs xs ++ [⟨j, y⟩]) := by
  have := h.2.2
  rw [← rightInputs, rightInputs_inr] at this
  exact this.resolve_left (by simp)

end Interface

namespace SimulationOn

variable {S₁ S₂ I : Type} {X Y : I → Type} {E : List (Σ i, X i) → Prop}
  {step₁ : ProbStep S₁ I X Y} {step₂ : ProbStep S₂ I X Y}

/-- A simulation, with its target step rewritten. -/
def castTarget {step₂' : ProbStep S₂ I X Y} (σ : SimulationOn E step₁ step₂) (h : step₂ = step₂') :
    SimulationOn E step₁ step₂' :=
  ⟨σ.kernel, σ.inv, σ.pres, fun xs s x hs hx => h ▸ σ.sim xs s x hs hx⟩

/-- **A source of `q` samples is fresh sampling remembering its reads.** -/
noncomputable def source {Z : Type} [Fintype Z] (law : Distribution.ProbDist Z) (q : ℕ) :
    SimulationOn (Interface.source Z q).domain (ProbStep.readFresh law)
      (ProbStep.ofDeterministic (Interface.sourceStep (q := q) law)) where
  kernel := ProbStep.tableKernel law q
  inv xs r := r.length = xs.length
  pres xs r x hr _ p hp := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (support_fTransform_subset _ _ hp)
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp (support_fTransform_subset _ _ hz)
    simpa [ProbStep.tagged] using hr
  sim xs r x hr hx := ProbStep.simulatesAt_source law q r (by
    have := hx.2
    simp at this
    omega) x

/-- **Forgetting the reads of fresh samples.** -/
noncomputable def forgetReads {Z : Type} {E : List (Σ _ : Unit, Unit) → Prop}
    (law : Distribution.ProbDist Z) :
    SimulationOn E (ProbStep.readFresh law) (ProbStep.fresh law) :=
  ⟨fun _ => Distribution.ProbDist.single (), fun _ _ => True, fun _ _ _ _ _ _ _ => trivial,
    fun _ r x _ _ => ProbStep.simulatesAt_forgetReads law r x⟩

/-- **Simulations side by side**, on the parallel domain. -/
noncomputable def parallel {A B : Interface} {S₁ T₁ S₂ T₂ : Type}
    {f₁ : ProbStep S₁ A.I A.X A.Y} {f₂ : ProbStep S₂ A.I A.X A.Y} {g₁ : ProbStep T₁ B.I B.X B.Y}
    {g₂ : ProbStep T₂ B.I B.X B.Y} (σ : SimulationOn A.domain f₁ f₂)
    (τ : SimulationOn B.domain g₁ g₂) :
    SimulationOn (Interface.tensor A B).domain (ProbStep.parallel f₁ g₁)
      (ProbStep.parallel f₂ g₂) where
  kernel := ProbStep.prodKernel σ.kernel τ.kernel
  inv xs st := σ.inv (Interface.leftInputs xs) st.1 ∧ τ.inv (Interface.rightInputs xs) st.2
  pres xs st x h hx p hp := by
    obtain ⟨a, b⟩ := st
    obtain ⟨l, x⟩ := x
    cases l with
    | inl i =>
      rw [ProbStep.outcome_parallel_inl] at hp
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp (support_fTransform_subset _ _ hp)
      refine ⟨?_, ?_⟩
      · rw [Interface.leftInputs_inl]
        exact σ.pres _ a ⟨i, x⟩ h.1 (Interface.tensor_domain_inl hx) p' hp'
      · rw [Interface.rightInputs_inl]
        exact h.2
    | inr j =>
      rw [ProbStep.outcome_parallel_inr] at hp
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp (support_fTransform_subset _ _ hp)
      refine ⟨?_, ?_⟩
      · rw [Interface.leftInputs_inr]
        exact h.1
      · rw [Interface.rightInputs_inr]
        exact τ.pres _ b ⟨j, x⟩ h.2 (Interface.tensor_domain_inr hx) p' hp'
  sim xs st x h hx := by
    obtain ⟨a, b⟩ := st
    obtain ⟨l, x⟩ := x
    cases l with
    | inl i =>
      exact ProbStep.simulatesAt_parallel_inl g₁ g₂ τ.kernel
        (σ.sim _ a ⟨i, x⟩ h.1 (Interface.tensor_domain_inl hx)) b
    | inr j =>
      exact ProbStep.simulatesAt_parallel_inr f₁ f₂ σ.kernel
        (τ.sim _ b ⟨j, x⟩ h.2 (Interface.tensor_domain_inr hx)) a

/-- **A program making at most `b` inside queries per invocation**, along a simulation of its
inside automata: its inside queries stay in the inside domain on `b * A.bound` queries. -/
noncomputable def ofProgram {A B : Interface} {S R₁ R₂ : Type}
    {stepR₁ : ProbStep R₁ B.I B.X B.Y} {stepR₂ : ProbStep R₂ B.I B.X B.Y}
    (σ : SimulationOn B.domain stepR₁ stepR₂) (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ}
    (hb : P.Bounded b) (hB : ∀ xs, xs ≠ [] → xs.length ≤ b * A.bound → B.domain xs) :
    SimulationOn A.domain (P.probCombine stepR₁ hb) (P.probCombine stepR₂ hb) :=
  have good : ∀ xs (sr : S × R₁) x τ, τ.length ≤ b * xs.length → A.domain (xs ++ [x]) →
      P.AdmitsInvocation B.domain sr.1 x.1 x.2 τ := fun xs sr x τ hl hx h q hc hq => hB _
    (by simp) (by
      have h1 := hb sr.1 x.1 x.2 h q hc hq
      have h2 := A.length_le _ hx
      simp at h2 ⊢
      nlinarith)
  { kernel := Program.insideKernel σ.kernel
    inv := fun xs sr => ∃ τ, σ.inv τ sr.2 ∧ τ.length ≤ b * xs.length
    pres := fun xs sr x ⟨τ, hτ, hl⟩ hx p hp => by
      obtain ⟨hf, hcf, hinv⟩ := Program.probCombine_support P hb σ.pres hτ
        (good xs sr x τ hl hx) p hp
      refine ⟨τ ++ hf.map Prod.fst, hinv, ?_⟩
      have := Program.Consistent.length_le hb hcf
      simp
      nlinarith
    sim := fun xs sr x ⟨τ, hτ, hl⟩ hx =>
      Program.simulatesAt_probCombine P hb σ.sim σ.pres hτ (good xs sr x τ hl hx) }

/-- **A port-preserving program**, along a simulation of its inside automata: its inside queries
stay in the inside domain, at most `b` per invocation and at each label `ι o` at most as often as
it is queried at `o`. -/
noncomputable def ofPreservingProgram {A B : Interface} {S R₁ R₂ : Type}
    {stepR₁ : ProbStep R₁ B.I B.X B.Y} {stepR₂ : ProbStep R₂ B.I B.X B.Y}
    (σ : SimulationOn B.domain stepR₁ stepR₂) (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ}
    (hb : P.Bounded b) (ι : A.I → Option B.I) (hι : P.PortPreserving ι) (q : A.I → ℕ)
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) → B.domain ys) :
    SimulationOn A.domain (P.probCombine stepR₁ hb) (P.probCombine stepR₂ hb) :=
  have count : ∀ xs (x : Σ o, A.X o) (τ e : List (Σ j, B.X j)),
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j τ).length ≤
        (SystemAlgebra.restrict o xs).length) →
      (∀ o j, ι o = some j → SystemAlgebra.restrict j e = [] ∨
        (o = x.1 ∧ (SystemAlgebra.restrict j e).length = 1)) →
      ∀ o j, ι o = some j → (SystemAlgebra.restrict j (τ ++ e)).length ≤
        (SystemAlgebra.restrict o (xs ++ [x])).length := by
    intro xs x τ e hτ he o j hj
    rw [SystemAlgebra.restrict_append, SystemAlgebra.restrict_append, List.length_append,
      List.length_append, length_restrict_singleton]
    rcases he o j hj with h0 | ⟨ho, h1⟩
    · rw [h0, List.length_nil, Nat.add_zero]
      exact (hτ o j hj).trans (Nat.le_add_right _ _)
    · rw [h1, if_pos ho.symm]
      exact Nat.add_le_add_right (hτ o j hj) 1
  have good : ∀ xs (sr : S × R₁) x τ, τ.length ≤ b * xs.length →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j τ).length ≤
        (SystemAlgebra.restrict o xs).length) → A.domain (xs ++ [x]) →
      P.AdmitsInvocation B.domain sr.1 x.1 x.2 τ := fun xs sr x τ hl hc' hx h q₀ hc hq => by
    have hpre := Program.PreservesAt.restrict_length_le_snoc P (hι sr.1 x.1 x.2) hc hq
    refine hB _ (by simp) ?_ fun o j hj => ?_
    · have h1 := hb sr.1 x.1 x.2 h q₀ hc hq
      have h2 := A.length_le _ hx
      simp at h2 ⊢
      nlinarith
    · rw [List.append_assoc]
      exact (count xs x τ _ hc' (fun o' j' hj' => hpre o' j' hj') o j hj).trans (hA _ hx o)
  { kernel := Program.insideKernel σ.kernel
    inv := fun xs sr => ∃ τ, σ.inv τ sr.2 ∧ τ.length ≤ b * xs.length ∧
      ∀ o j, ι o = some j → (SystemAlgebra.restrict j τ).length ≤
        (SystemAlgebra.restrict o xs).length
    pres := fun xs sr x ⟨τ, hτ, hl, hc'⟩ hx p hp => by
      obtain ⟨hf, hcf, hinv⟩ := Program.probCombine_support P hb σ.pres hτ
        (good xs sr x τ hl hc' hx) p hp
      refine ⟨τ ++ hf.map Prod.fst, hinv, ?_, count xs x τ _ hc'
        (fun o j hj => Program.PreservesAt.restrict_length_le P (hι sr.1 x.1 x.2) hcf o j hj)⟩
      have := Program.Consistent.length_le hb hcf
      simp
      nlinarith
    sim := fun xs sr x ⟨τ, hτ, hl, hc'⟩ hx =>
      Program.simulatesAt_probCombine P hb σ.sim σ.pres hτ (good xs sr x τ hl hc' hx) }

/-- **A program at per-label budgets**, along a simulation of its inside automata: its inside
queries at `j` stay within `∑ o, c o j · q o`, which the inside interface admits. -/
noncomputable def ofLabelBoundedProgram {A B : Interface} {S R₁ R₂ : Type}
    {stepR₁ : ProbStep R₁ B.I B.X B.Y} {stepR₂ : ProbStep R₂ B.I B.X B.Y}
    (σ : SimulationOn B.domain stepR₁ stepR₂) (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ}
    (hb : P.Bounded b) (c : A.I → B.I → ℕ) (hc : P.LabelBounded c) (q : A.I → ℕ)
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : B.AdmitsLabelBudget fun j => ∑ o, c o j * q o) :
    SimulationOn A.domain (P.probCombine stepR₁ hb) (P.probCombine stepR₂ hb) :=
  have step : ∀ xs (x : Σ o, A.X o) (τ e : List (Σ j, B.X j)),
      (∀ j, (SystemAlgebra.restrict j τ).length ≤
        ∑ o, c o j * (SystemAlgebra.restrict o xs).length) →
      (∀ j, (SystemAlgebra.restrict j e).length ≤ c x.1 j) →
      ∀ j, (SystemAlgebra.restrict j (τ ++ e)).length ≤
        ∑ o, c o j * (SystemAlgebra.restrict o (xs ++ [x])).length := by
    intro xs x τ e hτ he j
    rw [SystemAlgebra.restrict_append, List.length_append]
    have hsum : ∑ o, c o j * (SystemAlgebra.restrict o (xs ++ [x])).length =
        ∑ o, c o j * (SystemAlgebra.restrict o xs).length + c x.1 j := by
      simp only [SystemAlgebra.restrict_append, List.length_append,
        SystemAlgebra.length_restrict_singleton, mul_add, Finset.sum_add_distrib, mul_ite, mul_one,
        mul_zero]
      simp
    rw [hsum]
    exact Nat.add_le_add (hτ j) (he j)
  have good : ∀ xs (sr : S × R₁) x τ,
      (∀ j, (SystemAlgebra.restrict j τ).length ≤
        ∑ o, c o j * (SystemAlgebra.restrict o xs).length) → A.domain (xs ++ [x]) →
      P.AdmitsInvocation B.domain sr.1 x.1 x.2 τ := fun xs sr x τ hτ hx h q₀ hc' hq => by
    refine hB _ (by simp) fun j => ?_
    rw [List.append_assoc]
    refine (step xs x τ _ hτ (Program.LabelCallBound.restrict_length_le_snoc P
      (hc sr.1 x.1 x.2) hc' hq) j).trans (Finset.sum_le_sum fun o _ => ?_)
    exact Nat.mul_le_mul_left _ (hA _ hx o)
  { kernel := Program.insideKernel σ.kernel
    inv := fun xs sr => ∃ τ, σ.inv τ sr.2 ∧
      ∀ j, (SystemAlgebra.restrict j τ).length ≤ ∑ o, c o j * (SystemAlgebra.restrict o xs).length
    pres := fun xs sr x ⟨τ, hτ, hc'⟩ hx p hp => by
      obtain ⟨hf, hcf, hinv⟩ := Program.probCombine_support P hb σ.pres hτ
        (good xs sr x τ hc' hx) p hp
      exact ⟨τ ++ hf.map Prod.fst, hinv, step xs x τ _ hc'
        (Program.LabelCallBound.restrict_length_le P (hc sr.1 x.1 x.2) hcf)⟩
    sim := fun xs sr x ⟨τ, hτ, hc'⟩ hx =>
      Program.simulatesAt_probCombine P hb σ.sim σ.pres hτ (good xs sr x τ hc' hx) }

end SimulationOn

/-- **A resource presented as fresh sampling**: an automaton reading tables of samples, and two
probabilistic steps that remember the samples read (`stepRF`) and forget them (`stepF`), with the
simulations relating them on the domain. -/
structure FreshSampling (B : Interface) (R : Interface.Resource B) where
  {D : Type}
  {RF : Type}
  {F : Type}
  /-- The automaton reading tables of samples. -/
  stepD : D → (j : B.I) → B.X j → D × B.Y j
  initD : Distribution.ProbDist D
  eq : R = Interface.Resource.ofAutomaton B stepD initD
  /-- Fresh sampling, remembering the samples read. -/
  stepRF : ProbStep RF B.I B.X B.Y
  initRF : RF
  /-- Fresh sampling. -/
  stepF : ProbStep F B.I B.X B.Y
  initF : F
  toTable : SimulationOn B.domain stepRF (ProbStep.ofDeterministic stepD)
  toFresh : SimulationOn B.domain stepRF stepF
  inv_table : toTable.inv [] initRF
  inv_fresh : toFresh.inv [] initRF
  init_table : initD.1 = (toTable.kernel initRF).1
  init_fresh : (toFresh.kernel initRF).1 = Finsupp.single initF 1

namespace FreshSampling

variable {B : Interface} {R : Interface.Resource B}

/-- **The resource is fresh sampling.** -/
lemma eq_fresh (Φ : FreshSampling B R) :
    R = Interface.Resource.ofProbAutomaton B Φ.stepF (Distribution.ProbDist.single Φ.initF) := by
  have hsingle : ∀ r ∈ (Distribution.ProbDist.single Φ.initRF).1.support, r = Φ.initRF :=
    fun r hr => (Finsupp.mem_support_single _ _ _).mp hr |>.1
  refine Φ.eq.trans ?_
  rw [Interface.Resource.ofAutomaton_eq_ofProbAutomaton]
  refine (Interface.Resource.ofProbAutomaton_eq_of_simulationOn Φ.toTable
    (Distribution.ProbDist.single Φ.initRF) _
      (fun r hr => hsingle r hr ▸ Φ.inv_table) ?_).symm.trans
    (Interface.Resource.ofProbAutomaton_eq_of_simulationOn Φ.toFresh
      (Distribution.ProbDist.single Φ.initRF) _ (fun r hr => hsingle r hr ▸ Φ.inv_fresh) ?_)
  · change _ = bindK (Finsupp.single _ 1) _
    rw [bindK_single, one_smul, Φ.init_table]
  · change _ = bindK (Finsupp.single _ 1) _
    rw [bindK_single, one_smul, Φ.init_fresh]
    rfl

/-- The same presentation of an equal resource. -/
noncomputable def cast (Φ : FreshSampling B R) {R' : Interface.Resource B} (h : R = R') :
    FreshSampling B R' where
  stepD := Φ.stepD
  initD := Φ.initD
  eq := h ▸ Φ.eq
  stepRF := Φ.stepRF
  initRF := Φ.initRF
  stepF := Φ.stepF
  initF := Φ.initF
  toTable := Φ.toTable
  toFresh := Φ.toFresh
  inv_table := Φ.inv_table
  inv_fresh := Φ.inv_fresh
  init_table := Φ.init_table
  init_fresh := Φ.init_fresh

open CategoryTheory in
/-- **A converter with its sources beside the inside interface**, `α ≫ rightContext J S`,
attached to a resource with a presentation: `α` on the resource beside the sources. -/
noncomputable def ofRightContext {A J E : Interface} {S : Interface.Resource E}
    (α : A ⟶ Interface.tensor J E) {R₀ : Interface.Resource J}
    (Φ : FreshSampling A (α • Interface.parallel R₀ S)) :
    FreshSampling A ((α ≫ Interface.rightContext J S) • R₀) :=
  Φ.cast (by rw [Interface.comp_smul, Interface.attach_rightContext])

/-- **A source of `q` samples is fresh sampling.** -/
noncomputable def source {Z : Type} [Fintype Z] (law : Distribution.ProbDist Z) (q : ℕ) :
    FreshSampling (Interface.source Z q) (Interface.Resource.source law q) where
  stepD := Interface.sourceStep law
  initD := ⟨fTransform (fun t => (t, 0)) (pi fun _ : Fin q => law.1),
    fTransform_isProbDist _ (pi_isProbDist fun _ => law.2)⟩
  eq := rfl
  stepRF := ProbStep.readFresh law
  initRF := []
  stepF := ProbStep.fresh law
  initF := ()
  toTable := SimulationOn.source law q
  toFresh := SimulationOn.forgetReads law
  inv_table := rfl
  inv_fresh := trivial
  init_table := (ProbStep.tableKernel_nil law q).symm
  init_fresh := rfl

/-- **Fresh sampling side by side.** -/
noncomputable def parallel {A : Interface} {R₁ : Interface.Resource A}
    (Φ₁ : FreshSampling A R₁) (Φ₂ : FreshSampling B R) :
    FreshSampling (Interface.tensor A B) (Interface.parallel R₁ R) where
  stepD := parallelStep Φ₁.stepD Φ₂.stepD
  initD := ⟨prod Φ₁.initD.1 Φ₂.initD.1, prod_isProbDist _ _ Φ₁.initD.2 Φ₂.initD.2⟩
  eq := (congrArg₂ Interface.parallel Φ₁.eq Φ₂.eq).trans (Interface.parallel_ofAutomaton _ _ _ _)
  stepRF := ProbStep.parallel Φ₁.stepRF Φ₂.stepRF
  initRF := (Φ₁.initRF, Φ₂.initRF)
  stepF := ProbStep.parallel Φ₁.stepF Φ₂.stepF
  initF := (Φ₁.initF, Φ₂.initF)
  toTable := (Φ₁.toTable.parallel Φ₂.toTable).castTarget
    (ProbStep.ofDeterministic_parallelStep _ _).symm
  toFresh := Φ₁.toFresh.parallel Φ₂.toFresh
  inv_table := ⟨Φ₁.inv_table, Φ₂.inv_table⟩
  inv_fresh := ⟨Φ₁.inv_fresh, Φ₂.inv_fresh⟩
  init_table := by
    change _ = (ProbStep.prodKernel Φ₁.toTable.kernel Φ₂.toTable.kernel (Φ₁.initRF, Φ₂.initRF)).1
    rw [ProbStep.prodKernel_val, ← Φ₁.init_table, ← Φ₂.init_table]
  init_fresh := by
    change (ProbStep.prodKernel Φ₁.toFresh.kernel Φ₂.toFresh.kernel (Φ₁.initRF, Φ₂.initRF)).1 = _
    rw [ProbStep.prodKernel_val, Φ₁.init_fresh, Φ₂.init_fresh]
    ext p
    rw [prod_apply, Finsupp.single_apply, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h₁ : Φ₁.initF = p.1 <;> by_cases h₂ : Φ₂.initF = p.2 <;> simp [h₁, h₂, Prod.ext_iff]

/-- **The converter of a program on fresh sampling is fresh sampling.** -/
noncomputable def ofProgram {A : Interface} {S : Type} (Φ : FreshSampling B R) (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    (hB : ∀ xs, xs ≠ [] → xs.length ≤ b * A.bound → B.domain xs) :
    FreshSampling A (Interface.Converter.ofProgram s P hb hB • R) where
  stepD := P.combine Φ.stepD hb
  initD := ⟨fTransform (fun r => (s, r)) Φ.initD.1, fTransform_isProbDist _ Φ.initD.2⟩
  eq := (congrArg _ Φ.eq).trans (Interface.Converter.ofProgram_smul_ofAutomaton s P hb hB _ _)
  stepRF := P.probCombine Φ.stepRF hb
  initRF := (s, Φ.initRF)
  stepF := P.probCombine Φ.stepF hb
  initF := (s, Φ.initF)
  toTable := (Φ.toTable.ofProgram P hb hB).castTarget (Program.ofDeterministic_combine _ _).symm
  toFresh := Φ.toFresh.ofProgram P hb hB
  inv_table := ⟨[], Φ.inv_table, le_refl _⟩
  inv_fresh := ⟨[], Φ.inv_fresh, le_refl _⟩
  init_table := by
    change _ = fTransform (fun r₂ => (s, r₂)) (Φ.toTable.kernel Φ.initRF).1
    rw [← Φ.init_table]
  init_fresh := by
    change fTransform (fun r₂ => (s, r₂)) (Φ.toFresh.kernel Φ.initRF).1 = _
    rw [Φ.init_fresh]
    simp [fTransform]

/-- **The converter of a port-preserving program on fresh sampling is fresh sampling.** -/
noncomputable def ofPreservingProgram {A : Interface} {S : Type} (Φ : FreshSampling B R) (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b) (ι : A.I → Option B.I)
    (hι : P.PortPreserving ι) (q : A.I → ℕ)
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) → B.domain ys) :
    FreshSampling A (Interface.Converter.ofPreservingProgram s P hb ι hι q hA hB • R) where
  stepD := P.combine Φ.stepD hb
  initD := ⟨fTransform (fun r => (s, r)) Φ.initD.1, fTransform_isProbDist _ Φ.initD.2⟩
  eq := (congrArg _ Φ.eq).trans
    (Interface.Converter.ofPreservingProgram_smul_ofAutomaton s P hb ι hι q hA hB _ _)
  stepRF := P.probCombine Φ.stepRF hb
  initRF := (s, Φ.initRF)
  stepF := P.probCombine Φ.stepF hb
  initF := (s, Φ.initF)
  toTable := (Φ.toTable.ofPreservingProgram P hb ι hι q hA hB).castTarget
    (Program.ofDeterministic_combine _ _).symm
  toFresh := Φ.toFresh.ofPreservingProgram P hb ι hι q hA hB
  inv_table := ⟨[], Φ.inv_table, le_refl _, fun _ _ _ => by simp⟩
  inv_fresh := ⟨[], Φ.inv_fresh, le_refl _, fun _ _ _ => by simp⟩
  init_table := by
    change _ = fTransform (fun r₂ => (s, r₂)) (Φ.toTable.kernel Φ.initRF).1
    rw [← Φ.init_table]
  init_fresh := by
    change fTransform (fun r₂ => (s, r₂)) (Φ.toFresh.kernel Φ.initRF).1 = _
    rw [Φ.init_fresh]
    simp [fTransform]

/-- **The converter of a program at per-label budgets on fresh sampling is fresh sampling.** -/
noncomputable def ofLabelBoundedProgram {A : Interface} {S : Type} (Φ : FreshSampling B R) (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b) (c : A.I → B.I → ℕ)
    (hc : P.LabelBounded c) (q : A.I → ℕ)
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : B.AdmitsLabelBudget fun j => ∑ o, c o j * q o) :
    FreshSampling A (Interface.Converter.ofLabelBoundedProgram s P hb c hc q hA hB • R) where
  stepD := P.combine Φ.stepD hb
  initD := ⟨fTransform (fun r => (s, r)) Φ.initD.1, fTransform_isProbDist _ Φ.initD.2⟩
  eq := (congrArg _ Φ.eq).trans
    (Interface.ofDDC_ofProgramOn_smul_ofAutomaton s P hb _ _ _)
  stepRF := P.probCombine Φ.stepRF hb
  initRF := (s, Φ.initRF)
  stepF := P.probCombine Φ.stepF hb
  initF := (s, Φ.initF)
  toTable := (Φ.toTable.ofLabelBoundedProgram P hb c hc q hA hB).castTarget
    (Program.ofDeterministic_combine _ _).symm
  toFresh := Φ.toFresh.ofLabelBoundedProgram P hb c hc q hA hB
  inv_table := ⟨[], Φ.inv_table, fun _ => by simp⟩
  inv_fresh := ⟨[], Φ.inv_fresh, fun _ => by simp⟩
  init_table := by
    change _ = fTransform (fun r₂ => (s, r₂)) (Φ.toTable.kernel Φ.initRF).1
    rw [← Φ.init_table]
  init_fresh := by
    change fTransform (fun r₂ => (s, r₂)) (Φ.toFresh.kernel Φ.initRF).1 = _
    rw [Φ.init_fresh]
    simp [fTransform]

end FreshSampling

/-- **A source is fresh sampling**: the source of `q` samples of `law` answers each query with an
independent sample. -/
lemma Interface.Resource.source_eq_fresh {Z : Type} [Fintype Z] (law : Distribution.ProbDist Z)
    (q : ℕ) :
    Interface.Resource.source law q = Interface.Resource.ofProbAutomaton (Interface.source Z q)
      (ProbStep.fresh law) (Distribution.ProbDist.single ()) :=
  (FreshSampling.source law q).eq_fresh

end SystemAlgebra

/-! ## Constant kernels, product tables, and maps of states under an invariant -/

namespace Probability.Distribution

variable {A B : Type*}

/-- A kernel that ignores its sample: the mixture is the kernel scaled by the weight. -/
lemma bindK_const (μ : Distribution A) (ν : Distribution B) :
    bindK μ (fun _ => ν) = μ.weight • ν := by
  induction μ using Finsupp.induction_linear with
  | zero => simp [weight]
  | add μ μ' h h' => rw [bindK_add, h, h', weight_add, add_smul]
  | single a w => rw [bindK_single, weight_single]

/-- **An unused sample marginalizes away**: a kernel that ignores a sample of weight one. -/
lemma bindK_const_of_weight {μ : Distribution A} (hμ : μ.weight = 1) (ν : Distribution B) :
    bindK μ (fun _ => ν) = ν := by
  rw [bindK_const, hμ, one_smul]

/-- **The marginal of independent samples**: a kernel reading one coordinate of independent
samples of weight one is the kernel on that coordinate. -/
lemma bindK_pi_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Distribution A)
    (hμ : ∀ j, (μ j).weight = 1) (i : ι) (F : A → Distribution B) :
    bindK (pi μ) (fun t => F (t i)) = bindK (μ i) F := by
  rw [pi_eq_bindK_update μ i, bindK_bindK]
  refine bindK_congr fun z _ => ?_
  rw [bindK_congr (g := fun _ => F z) fun t ht => by rw [eq_of_mem_support_pi_update μ i z ht]]
  refine bindK_const_of_weight ?_ _
  rw [weight_pi]
  refine Finset.prod_eq_one fun j _ => ?_
  by_cases h : j = i
  · subst h
    rw [Function.update_self, weight_single]
  · rw [Function.update_of_ne h, hμ]

/-- **Sequential composition as a mixture**: the law of `b ← f a` for `a ← P`. -/
lemma ProbDist.bind_val [Fintype A] [DecidableEq A] (P : ProbDist A) (f : A → ProbDist B) :
    (ProbDist.bind P f).1 = bindK P.1 fun a => (f a).1 := by
  show fTransform (fun x => x.2 x.1) (prod P.1 (Distribution.pi fun a => (f a).1)) = _
  rw [prod_eq_bindK, fTransform_bindK]
  refine bindK_congr fun a _ => ?_
  rw [fTransform_fTransform, fTransform_eq_bindK]
  exact (bindK_pi_apply _ (fun a => (f a).2.2) a (fun z => Finsupp.single z 1)).trans
    (bindK_single_one _)

end Probability.Distribution

namespace SystemAlgebra

open Probability Probability.Distribution

/-- **A simulation step along a map of states**: the steps of `step₂` from `φ s` are those of
`step₁` from `s` with the next state mapped by `φ`. -/
lemma ProbStep.simulatesAt_single {S₁ S₂ I : Type} {X Y : I → Type}
    {step₁ : ProbStep S₁ I X Y} {step₂ : ProbStep S₂ I X Y} {φ : S₁ → S₂} {s : S₁}
    {x : Σ i, X i}
    (h : step₂.outcome (φ s) x = fTransform (Prod.map φ id) (step₁.outcome s x)) :
    ProbStep.SimulatesAt step₁ step₂ (fun s => Distribution.ProbDist.single (φ s)) s x := by
  unfold ProbStep.SimulatesAt
  simp only [Distribution.ProbDist.single, bindK_single, one_smul]
  rw [h, ← bindK_single_comp]
  refine bindK_congr fun p _ => ?_
  simp [fTransform]
  rfl

/-- **Equal resources along a map of states on an invariant**: if an invariant of the states of
`step₁` holds initially and after every step, and from the states satisfying it the steps of
`step₂` from `φ s` are those of `step₁` from `s` with the next state mapped by `φ`, the
probabilistic automata are the same resource. -/
lemma Interface.Resource.ofProbAutomaton_eq_of_mapOn {T : Interface} {S₁ S₂ : Type}
    (step₁ : ProbStep S₁ T.I T.X T.Y) (step₂ : ProbStep S₂ T.I T.X T.Y)
    (init₁ : Distribution.ProbDist S₁) (init₂ : Distribution.ProbDist S₂) (φ : S₁ → S₂)
    (inv : S₁ → Prop) (hinv : ∀ s ∈ init₁.1.support, inv s)
    (hpres : ∀ s x, inv s → ∀ p ∈ (step₁.outcome s x).support, inv p.1)
    (hstep : ∀ s x, inv s →
      step₂.outcome (φ s) x = fTransform (Prod.map φ id) (step₁.outcome s x))
    (hinit : init₂.1 = fTransform φ init₁.1) :
    Interface.Resource.ofProbAutomaton T step₁ init₁ =
      Interface.Resource.ofProbAutomaton T step₂ init₂ :=
  Interface.Resource.ofProbAutomaton_eq_of_simulation step₁ step₂ init₁ init₂
    (fun s => Distribution.ProbDist.single (φ s)) (fun _ s => inv s) hinv
    (fun _ s x hs _ => hpres s x hs) (fun _ s x hs _ => ProbStep.simulatesAt_single (hstep s x hs))
    (by rw [hinit]; exact (bindK_single_comp _ _).symm)

end SystemAlgebra
