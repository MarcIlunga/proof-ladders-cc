import ConstructiveCryptography.Notation
import ProofLadders.Common.ProbAutomaton

/-!
# Identical until bad

Two random systems are identical until bad when the probabilities of their transcripts share a
common part, the probability of each transcript together with the event that bad has not
occurred, whole at the empty transcript. The first system then distinguishes itself from the
second only by the probability of bad: if each query `x` sets bad with probability at most
`β x`, and the queries of every possible transcript cost at most `ε` in total, the transcript
distance is at most `ε`. The proof follows the costs along the transcripts of an environment:
the cost of the queries made, minus the probability of bad, never decreases in expectation.

Two probabilistic automata on the same states, with a predicate `bad` on the states, are
identical until bad when, from the states that are not bad, their laws of the next state and
the reply agree on the next states that are not bad. Their common part is the forward algorithm
until bad: the sub-law of the states along the runs that have not reached a bad state. With a
bound `β i` on the probability that a step at the port `i` reaches a bad state, the per-port
systems with at most `q i` queries at each port are within `∑ i, q i · β i`.

Upstream candidates: `RandomSystem.le_sum_tSupp` and
`RandomSystem.transcriptDistance_le_of_untilBad`, for `RandomSystems.Distance.Decision`;
`ProbStep.beliefUntilBad` and its lemmas, and `Interface.Resource.distance_ofProbAutomaton_le`,
for `ConstructiveCryptography.Automaton`, beside `Interface.Resource.ofProbAutomaton`.

## Main definitions

* `ProbStep.beliefUntilBad step D bad init`: the forward algorithm until bad

## Main results

* `RandomSystem.transcriptDistance_le_of_untilBad`: random systems identical until bad are
  within the cost of their queries
* `ProbStep.beliefUntilBad_le_belief`, `ProbStep.beliefUntilBad_eq`,
  `ProbStep.weight_beliefUntilBad_snoc_ge`: the forward algorithm until bad is below the forward
  algorithm, is common to automata identical until bad, and loses at most the probability of
  reaching bad at each query
* `Interface.Resource.distance_ofProbAutomaton_le`: probabilistic automata identical until bad
  are within `∑ i, q i · β i` at per-port budgets
-/

namespace SystemAlgebra

open Classical Probability Probability.Distribution

namespace RandomSystem

section Potential

variable {A B : Type} [Fintype A] [Fintype B] {D : Domain A B} {R : RandomSystem A B D}
  {σ : List B →. A}

/-- **A value that grows along the transcripts in total**: if at each possible transcript at
which `σ` queries, the values at its extensions by the possible replies add up to at least its
value, then the values on the transcripts within `m` rounds add up to at least the value at the
empty transcript. -/
lemma le_sum_tSupp (f : List (A × B) → ℝ)
    (hf : ∀ h x, Cons σ h → R h ≠ 0 → x ∈ σ (h.map Prod.snd) →
      f h ≤ ∑ y ∈ (R.extensionLaw h x).support, f (h ++ [(x, y)])) :
    ∀ m, f [] ≤ ∑ h ∈ tSupp R σ m, if Good σ m h then f h else 0 := by
  intro m
  induction m with
  | zero => simp [tSupp, Good, Done, cons_nil]
  | succ m ih =>
    rw [tSupp, Finset.sum_biUnion]
    · refine ih.trans (Finset.sum_le_sum fun h hh => ?_)
      obtain ⟨hc, hd'⟩ := tSupp_good hh
      rw [if_pos ⟨hc, hd'⟩]
      split_ifs with hd
      · rw [Finset.sum_image (fun y _ y' _ e => by simpa using e)]
        have hl : h.length = m := by
          rcases hd' with h | ⟨_, h⟩
          · exact h
          · exact absurd hd h
        refine (hf h _ hc (tSupp_possible hh) (Part.get_mem hd)).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [if_pos ⟨cons_snoc.mpr ⟨hc, Part.get_mem hd⟩, Or.inl (by simp [hl])⟩]
      · rw [Finset.sum_singleton,
          if_pos ⟨hc, Or.inr ⟨by rcases hd' with h | ⟨h, _⟩ <;> omega, hd⟩⟩]
    · intro h hh h' hh' hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro g hg hg'
      obtain ⟨hc, hd⟩ := tSupp_good (m := m) hh
      obtain ⟨hc', hd'⟩ := tSupp_good (m := m) hh'
      split_ifs at hg hg' with e1 e2 e2
      · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hg
        obtain ⟨y', -, e⟩ := Finset.mem_image.mp hg'
        exact hne (List.append_inj' e rfl).1.symm
      · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hg
        rw [Finset.mem_singleton] at hg'
        have hl : h.length = m := by rcases hd with h | ⟨_, h⟩; exact h; exact absurd e1 h
        have := congrArg List.length hg'
        rcases hd' with h | ⟨h, _⟩ <;> simp at this <;> omega
      · obtain ⟨y', -, e⟩ := Finset.mem_image.mp hg'
        rw [Finset.mem_singleton] at hg
        have hl : h'.length = m := by rcases hd' with h | ⟨_, h⟩; exact h; exact absurd e2 h
        have := congrArg List.length (e.trans hg)
        rcases hd with h | ⟨h, _⟩ <;> simp at this <;> omega
      · rw [Finset.mem_singleton] at hg hg'
        exact hne (hg.symm.trans hg')

end Potential

variable {I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {𝒟 : Domain (Σ i, X i) (Σ i, Y i)}

/-- **Identical until bad**: if the probabilities of the transcripts of `R₁` and `R₂` are both at
least `g`, whole at the empty transcript, and `g` loses at most `β x` times the probability of
the transcript at each admitted query `x`, then `R₁` and `R₂` are within the largest cost of the
queries of a possible transcript of `R₁`. -/
lemma transcriptDistance_le_of_untilBad {R₁ R₂ : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟}
    (hR₁ : R₁.RepliesAtQueriedInterface) (g : List ((Σ i, X i) × (Σ i, Y i)) → ℝ)
    (hg₁ : ∀ h, g h ≤ R₁ h) (hg₂ : ∀ h, g h ≤ R₂ h) (hnil : g [] = 1)
    (β : (Σ i, X i) → ℝ)
    (hloss : ∀ h x, 𝒟 h x → g h - ∑ y, g (h ++ [(x, y)]) ≤ β x * R₁ h) {ε : ℝ}
    (hcost : ∀ h, R₁ h ≠ 0 → (h.map fun z => β z.1).sum ≤ ε) :
    R₁.transcriptDistance R₂ ≤ ENNReal.ofReal ε := by
  refine iSup_le fun E => iSup_le fun n => iSup_le fun _ => iSup_le fun hc => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hC := hc R₁ hR₁
  set c : List ((Σ i, X i) × (Σ i, Y i)) → ℝ := fun h => (h.map fun z => β z.1).sum with hcdef
  -- The cost of the queries made, minus the probability of bad.
  set Φ : List ((Σ i, X i) × (Σ i, Y i)) → ℝ := fun h => c h * R₁ h - (R₁ h - g h) with hΦdef
  have hsnoc : ∀ h x y, c (h ++ [(x, y)]) = c h + β x := fun h x y => by
    simp [hcdef]
  have hgrow : ∀ m, Φ [] ≤ ∑ h ∈ tSupp R₁ E.1 m, if Good E.1 m h then Φ h else 0 := by
    refine le_sum_tSupp Φ fun h x hcons hp hx => ?_
    have hd := hC h x hcons hp hx
    have hw := R₁.extensionLaw_weight h x
    rw [if_pos hd, weight_eq_sum] at hw
    simp only [extensionLaw_apply] at hw
    -- Off the possible replies the value is at most `0`.
    have hout : ∀ y ∈ Finset.univ \ (R₁.extensionLaw h x).support, Φ (h ++ [(x, y)]) ≤ 0 := by
      intro y hy
      have h0 : R₁ (h ++ [(x, y)]) = 0 := by
        have := (Finset.mem_sdiff.mp hy).2
        rwa [Finsupp.notMem_support_iff, extensionLaw_apply] at this
      simp only [hΦdef, h0, mul_zero, zero_sub, sub_neg_eq_add, zero_add]
      exact h0 ▸ hg₁ _
    have hsplit := Finset.sum_sdiff (f := fun y => Φ (h ++ [(x, y)]))
      (Finset.subset_univ (R₁.extensionLaw h x).support)
    have hall : Φ h ≤ ∑ y, Φ (h ++ [(x, y)]) := by
      have e : ∑ y, Φ (h ++ [(x, y)]) =
          (c h + β x) * R₁ h - R₁ h + ∑ y, g (h ++ [(x, y)]) := by
        simp only [hΦdef, hsnoc]
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hw]
        ring
      rw [e]
      linarith [hloss h x hd]
    linarith [Finset.sum_nonpos hout]
  have hΦnil : Φ [] = 0 := by simp [hΦdef, hcdef, R₁.mass_nil, hnil]
  -- The statistical distance is at most the probability of bad on the transcripts of `R₁`.
  have hsub : (R₁.sLaw E.1 n - R₂.sLaw E.1 n).support ⊆ tSupp R₁ E.1 n ∪ tSupp R₂ E.1 n := by
    refine Finsupp.support_sub.trans (Finset.union_subset_union ?_ ?_) <;>
      exact Finsupp.support_onFinset_subset
  rw [statDist_eq_sum_of_support_subset _ _ hsub]
  have hterm : ∀ h, max (R₁.sLaw E.1 n h - R₂.sLaw E.1 n h) 0 ≤
      if h ∈ tSupp R₁ E.1 n ∧ Good E.1 n h then R₁ h - g h else 0 := by
    intro h
    rw [sLaw_apply, sLaw_apply]
    by_cases hg : Good E.1 n h
    · by_cases ht : h ∈ tSupp R₁ E.1 n
      · rw [if_pos hg, if_pos hg, if_pos ⟨ht, hg⟩]
        exact max_le (by linarith [hg₂ h]) (by linarith [hg₁ h])
      · have h0 : R₁ h = 0 := by
          by_contra hne
          exact ht (mem_tSupp hg hne)
        rw [if_pos hg, if_pos hg, if_neg fun hh => ht hh.1, h0]
        exact max_le (by linarith [R₂.mass_nonneg h]) le_rfl
    · simp [hg]
  have hcost' : ∀ h ∈ tSupp R₁ E.1 n, c h ≤ ε := fun h hh => hcost h (tSupp_possible hh)
  have hone := sum_tSupp hC n
  calc ∑ h ∈ tSupp R₁ E.1 n ∪ tSupp R₂ E.1 n, max (R₁.sLaw E.1 n h - R₂.sLaw E.1 n h) 0
      ≤ ∑ h ∈ tSupp R₁ E.1 n ∪ tSupp R₂ E.1 n,
          if h ∈ tSupp R₁ E.1 n ∧ Good E.1 n h then R₁ h - g h else 0 :=
        Finset.sum_le_sum fun h _ => hterm h
    _ = ∑ h ∈ tSupp R₁ E.1 n, if Good E.1 n h then R₁ h - g h else 0 := by
        rw [← Finset.sum_filter, ← Finset.sum_filter]
        congr 1
        ext h
        simp only [Finset.mem_filter, Finset.mem_union]
        tauto
    _ = ∑ h ∈ tSupp R₁ E.1 n, ((if Good E.1 n h then c h * R₁ h else 0) -
          if Good E.1 n h then Φ h else 0) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        split_ifs <;> simp [hΦdef]
    _ ≤ ∑ h ∈ tSupp R₁ E.1 n, if Good E.1 n h then ε * R₁ h else 0 := by
        rw [Finset.sum_sub_distrib]
        have hle : ∑ h ∈ tSupp R₁ E.1 n, (if Good E.1 n h then c h * R₁ h else 0) ≤
            ∑ h ∈ tSupp R₁ E.1 n, if Good E.1 n h then ε * R₁ h else 0 :=
          Finset.sum_le_sum fun h hh => by
            split_ifs
            · exact mul_le_mul_of_nonneg_right (hcost' h hh) (R₁.mass_nonneg h)
            · exact le_rfl
        linarith [hgrow n]
    _ = ε * ∑ h ∈ tSupp R₁ E.1 n, if Good E.1 n h then R₁ h else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun h _ => ?_
        split_ifs <;> simp
    _ = ε := by rw [hone, mul_one]

end RandomSystem

namespace ProbStep

variable {S I : Type} {X Y : I → Type} (step : ProbStep S I X Y)
  (D : Domain (Σ i, X i) (Σ i, Y i)) (bad : S → Prop) (init : Distribution S)

/-- The forward algorithm until bad on a reversed transcript. -/
noncomputable def beliefUntilBadRev : List ((Σ i, X i) × (Σ i, Y i)) → Distribution S
  | [] => init.restrict fun s => ¬ bad s
  | e :: rh => if D rh.reverse e.1 then
      (step.transition (beliefUntilBadRev rh) e.1 e.2).restrict fun s => ¬ bad s else 0

/-- **The forward algorithm until bad**: the sub-law of the states after the transcript `h`
along the runs that have not reached a bad state. -/
noncomputable def beliefUntilBad (h : List ((Σ i, X i) × (Σ i, Y i))) : Distribution S :=
  step.beliefUntilBadRev D bad init h.reverse

lemma beliefUntilBad_nil :
    step.beliefUntilBad D bad init [] = init.restrict fun s => ¬ bad s := rfl

lemma beliefUntilBad_snoc (h : List ((Σ i, X i) × (Σ i, Y i))) (x : Σ i, X i) (y : Σ i, Y i) :
    step.beliefUntilBad D bad init (h ++ [(x, y)]) =
      if D h x then (step.transition (step.beliefUntilBad D bad init h) x y).restrict
        (fun s => ¬ bad s) else 0 := by
  simp [beliefUntilBad, beliefUntilBadRev, List.reverse_append]

lemma beliefUntilBad_nonNeg (hinit : init.NonNeg) (h : List ((Σ i, X i) × (Σ i, Y i))) :
    (step.beliefUntilBad D bad init h).NonNeg := by
  induction h using List.reverseRecOn with
  | nil => exact hinit.restrict _
  | append_singleton h e ih =>
    rw [beliefUntilBad_snoc]
    split_ifs
    · exact (step.transition_nonNeg ih _ _).restrict _
    · exact fun _ => le_rfl

/-- The states reached with the reply `y` and not bad: the transition read off the law of the
next states that are not bad. -/
lemma restrict_transition (β : Distribution S) (x : Σ i, X i) (y : Σ i, Y i) :
    (step.transition β x y).restrict (fun s => ¬ bad s) = bindK β fun s =>
      fTransform Prod.fst (((step.outcome s x).restrict fun p => ¬ bad p.1).restrict
        fun p => p.2 = y) := by
  rw [transition, restrict_bindK]
  refine bindK_congr fun s _ => ?_
  rw [restrict_fTransform, restrict_restrict, restrict_restrict]
  exact congrArg _ (restrict_congr _ fun _ => and_comm)

/-- **The forward algorithm until bad is below the forward algorithm.** -/
lemma beliefUntilBad_le_belief (hinit : init.NonNeg) (h : List ((Σ i, X i) × (Σ i, Y i))) :
    (step.belief D init h - step.beliefUntilBad D bad init h).NonNeg := by
  induction h using List.reverseRecOn with
  | nil =>
    intro s
    simp only [belief_nil, beliefUntilBad_nil, Finsupp.coe_sub, Pi.sub_apply, restrict_apply]
    split_ifs <;> simp [hinit s]
  | append_singleton h e ih =>
    rw [belief_snoc, beliefUntilBad_snoc]
    split_ifs
    · intro s
      have hlin : step.transition (step.belief D init h) e.1 e.2 =
          step.transition (step.beliefUntilBad D bad init h) e.1 e.2 +
            step.transition (step.belief D init h - step.beliefUntilBad D bad init h) e.1 e.2 := by
        rw [transition, transition, transition, ← bindK_add, add_sub_cancel]
      have h₁ := step.transition_nonNeg ih e.1 e.2 s
      have h₂ := step.transition_nonNeg (step.beliefUntilBad_nonNeg D bad init hinit h) e.1 e.2 s
      rw [hlin]
      simp only [Finsupp.coe_sub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply, restrict_apply]
      split_ifs <;> linarith
    · intro s
      simp

variable {D bad init} in
/-- **Identical until bad, along the transcripts**: if, from the states that are not bad and
satisfy an invariant of the transcript so far, `step₁` and `step₂` agree on the next states
that are not bad, which keep the invariant, their forward algorithms until bad are equal. -/
lemma beliefUntilBad_eq (step₁ step₂ : ProbStep S I X Y)
    (inv : List ((Σ i, X i) × (Σ i, Y i)) → S → Prop)
    (hinit : ∀ s ∈ init.support, ¬ bad s → inv [] s)
    (hpres : ∀ h s x, inv h s → ¬ bad s → D h x →
      ∀ p ∈ (step₁.outcome s x).support, ¬ bad p.1 → inv (h ++ [(x, p.2)]) p.1)
    (hstep : ∀ h s x, inv h s → ¬ bad s → D h x →
      (step₁.outcome s x).restrict (fun p => ¬ bad p.1) =
        (step₂.outcome s x).restrict fun p => ¬ bad p.1)
    (h : List ((Σ i, X i) × (Σ i, Y i))) :
    (∀ s ∈ (step₁.beliefUntilBad D bad init h).support, inv h s ∧ ¬ bad s) ∧
      step₁.beliefUntilBad D bad init h = step₂.beliefUntilBad D bad init h := by
  induction h using List.reverseRecOn with
  | nil =>
    refine ⟨fun s hs => ?_, rfl⟩
    rw [beliefUntilBad_nil, Finsupp.mem_support_iff, restrict_apply] at hs
    by_cases hb : bad s
    · simp [hb] at hs
    · rw [if_pos hb] at hs
      exact ⟨hinit s (Finsupp.mem_support_iff.mpr hs) hb, hb⟩
  | append_singleton h e ih =>
    obtain ⟨x, y⟩ := e
    rw [beliefUntilBad_snoc, beliefUntilBad_snoc]
    split_ifs with hd
    · refine ⟨fun s hs => ?_, ?_⟩
      · rw [restrict_transition] at hs
        obtain ⟨s₀, hs₀, hs⟩ := mem_support_bindK hs
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (support_fTransform_subset _ _ hs)
        have hp' := support_restrict_subset _ _ hp
        rw [Finsupp.mem_support_iff, restrict_apply] at hp
        by_cases hy : p.2 = y
        swap
        · simp [hy] at hp
        rw [Finsupp.mem_support_iff, restrict_apply] at hp'
        by_cases hb : bad p.1
        · simp [hb] at hp'
        · rw [if_pos hb] at hp'
          obtain ⟨hinv, hb₀⟩ := ih.1 s₀ hs₀
          have := hpres h s₀ x hinv hb₀ hd p (Finsupp.mem_support_iff.mpr hp') hb
          rw [hy] at this
          exact ⟨this, hb⟩
      · rw [← ih.2, restrict_transition, restrict_transition]
        refine bindK_congr fun s hs => ?_
        obtain ⟨hinv, hb⟩ := ih.1 s hs
        rw [hstep h s x hinv hb hd]
    · exact ⟨fun s hs => absurd hs (by simp), rfl⟩

/-- **The loss of the forward algorithm until bad at a query**: if from each state it reaches,
the step at `x` reaches a bad state with probability at most `b`, the next states until bad keep
at least `1 - b` of its weight. -/
lemma weight_beliefUntilBad_snoc_ge [Fintype (Σ i, Y i)] (hinit : init.NonNeg)
    (h : List ((Σ i, X i) × (Σ i, Y i))) (x : Σ i, X i) (hd : D h x) {b : ℝ}
    (hb : ∀ s ∈ (step.beliefUntilBad D bad init h).support,
      (step.outcome s x).mass (fun p => bad p.1) ≤ b) :
    (1 - b) * (step.beliefUntilBad D bad init h).weight ≤
      ∑ y, (step.beliefUntilBad D bad init (h ++ [(x, y)])).weight := by
  have hμ := step.beliefUntilBad_nonNeg D bad init hinit h
  set μ := step.beliefUntilBad D bad init h
  have hy : ∀ y, (step.beliefUntilBad D bad init (h ++ [(x, y)])).weight =
      ∑ s ∈ μ.support, μ s * ((step.outcome s x).restrict fun p => ¬ bad p.1).mass
        fun p => p.2 = y := by
    intro y
    rw [beliefUntilBad_snoc, if_pos hd, restrict_transition, weight_bindK]
    simp only [weight_fTransform, weight_restrict]
    rfl
  simp only [hy]
  rw [Finset.sum_comm, weight, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun s hs => ?_
  rw [← Finset.mul_sum, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (hμ s)
  have hfib := mass_eq_sum_mass_fiber ((step.outcome s x).restrict fun p => ¬ bad p.1)
    (fun _ => True) Prod.snd Finset.univ fun _ _ => Finset.mem_univ _
  simp only [true_and, mass_true, weight_restrict] at hfib
  rw [← hfib]
  have hc := mass_add_compl (step.outcome s x) fun p => bad p.1
  rw [weight_outcome] at hc
  linarith [hb s hs]

end ProbStep

/-- **Probabilistic automata identical until bad**, at per-port budgets: if, from the states that
are not bad and satisfy an invariant of the transcript so far, `step₁` and `step₂` agree on the
next states that are not bad, and a step of `step₁` at a query at the port `i` reaches a bad
state with probability at most `β i`, the automata with at most `q i` queries at each port `i`
are within `∑ i, q i · β i`. -/
lemma Interface.Resource.distance_ofProbAutomaton_le {T : Interface} {S : Type}
    (step₁ step₂ : ProbStep S T.I T.X T.Y) (init : Distribution.ProbDist S) (bad : S → Prop)
    (inv : List ((Σ i, T.X i) × (Σ i, T.Y i)) → S → Prop)
    (hinit : ∀ s ∈ init.1.support, inv [] s ∧ ¬ bad s)
    (hpres : ∀ h s x, inv h s → ¬ bad s → T.domain (h.map Prod.fst ++ [x]) →
      ∀ p ∈ (step₁.outcome s x).support, ¬ bad p.1 → inv (h ++ [(x, p.2)]) p.1)
    (hstep : ∀ h s x, inv h s → ¬ bad s → T.domain (h.map Prod.fst ++ [x]) →
      (step₁.outcome s x).restrict (fun p => ¬ bad p.1) =
        (step₂.outcome s x).restrict fun p => ¬ bad p.1)
    (q : T.I → ℕ) (hq : ∀ xs, T.domain xs → ∀ i, (SystemAlgebra.restrict i xs).length ≤ q i)
    (β : T.I → ℝ) (hβ₀ : ∀ i, 0 ≤ β i)
    (hβ : ∀ h s x, inv h s → ¬ bad s → T.domain (h.map Prod.fst ++ [x]) →
      (step₁.outcome s x).mass (fun p => bad p.1) ≤ β x.1) :
    Δ (Interface.Resource.ofProbAutomaton T step₁ init)
        (Interface.Resource.ofProbAutomaton T step₂ init) ≤
      ENNReal.ofReal (∑ i, q i * β i) := by
  rw [Interface.cc_distance_eq]
  have heq := ProbStep.beliefUntilBad_eq (D := T.inputDomain) (bad := bad) (init := init.1)
    step₁ step₂ inv (fun s hs _ => (hinit s hs).1) hpres hstep
  have hle : ∀ (step : ProbStep S T.I T.X T.Y) h,
      (step.beliefUntilBad T.inputDomain bad init.1 h).weight ≤
        (step.belief T.inputDomain init.1 h).weight := fun step h => by
    have := (step.beliefUntilBad_le_belief T.inputDomain bad init.1 init.2.1 h).weight_nonneg
    rw [weight_sub] at this
    linarith
  -- The cost of the queries of an admitted history.
  have hcount : ∀ xs : List (Σ i, T.X i),
      (xs.map fun x => β x.1).sum = ∑ i, ((SystemAlgebra.restrict i xs).length : ℝ) * β i := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, ih, show x :: xs = [x] ++ xs from rfl]
      simp only [restrict_append, List.length_append, length_restrict_singleton, Nat.cast_add,
        add_mul, Finset.sum_add_distrib, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul,
        one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine RandomSystem.transcriptDistance_le_of_untilBad
    (Interface.Resource.ofProbAutomaton T step₁ init).2
    (fun h => (step₁.beliefUntilBad T.inputDomain bad init.1 h).weight) (hle step₁)
    (fun h => (heq h).2 ▸ hle step₂ h) ?_ (fun x => β x.1) (fun h x hd => ?_) fun h hh => ?_
  · show (init.1.restrict fun s => ¬ bad s).weight = 1
    rw [weight_restrict, mass_congr_of_support _ (Q := fun _ => True)
      fun s hs => iff_true_intro (hinit s hs).2, mass_true, init.2.2]
  · have hgr := ProbStep.weight_beliefUntilBad_snoc_ge step₁ T.inputDomain bad init.1 init.2.1 h
      x hd (b := β x.1) fun s hs => hβ h s x ((heq h).1 s hs).1 ((heq h).1 s hs).2 hd
    have hR := hle step₁ h
    have hg0 := (step₁.beliefUntilBad_nonNeg T.inputDomain bad init.1 init.2.1 h).weight_nonneg
    change (step₁.beliefUntilBad T.inputDomain bad init.1 h).weight -
        ∑ y, (step₁.beliefUntilBad T.inputDomain bad init.1 (h ++ [(x, y)])).weight ≤
      β x.1 * (step₁.belief T.inputDomain init.1 h).weight
    nlinarith [hβ₀ x.1]
  · rcases List.eq_nil_or_concat h with rfl | ⟨h', z, rfl⟩
    · simpa using Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg (q i)) (hβ₀ i)
    · rw [List.concat_eq_append] at hh ⊢
      have hd : T.domain (h'.map Prod.fst ++ [z.1]) := by
        by_contra hn
        exact hh (RandomSystem.mass_eq_zero_of_not_admitted _ (D := T.inputDomain) hn z.2)
      have hmap : ((h' ++ [z]).map fun z => β z.1.1) = ((h'.map Prod.fst ++ [z.1]).map
          fun x => β x.1) := by simp
      rw [hmap, hcount]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
        (by exact_mod_cast hq _ hd i) (hβ₀ i)

end SystemAlgebra
