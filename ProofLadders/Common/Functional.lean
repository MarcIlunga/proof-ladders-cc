import ConstructiveCryptography.Functional
import ConstructiveCryptography.DSL.Converters
import ConstructiveCryptography.Context

/-!
# Converters on sampled functions

The machinery of the sampled-function model: a library is a function sampled once, and a
converter attached to a function is the function it computes against it. A sampling component is
an automaton over the tables of its sources, so it is sampled over its tables, and a sample at
which it answers by a function is that function.

Some declarations are restated from `cbc-mac-cc`, with its proofs; they are upstream candidates
there, and both applications use the same statements until they are upstreamed. The others are
new here. All are upstream candidates.

* `functionSystem`, `Program.answer`, `Program.feed_function`, `Program.inline_function` and
  `Program.trim_apply_ofProgramOn_function`, from `cbc-mac-cc`,
  `CBCMAC/Upstream/ProgramAttachment.lean`: the system of a function, an invocation run against
  a function, and a program attached to a function. Candidates for
  `RandomSystems.Converter.ProgramAttachment`, beside `inline_automatonSystem`.
* `functionSystem_eq_automatonSystem`, `automatonSystem_of_stored`: a function as an automaton,
  and an automaton that samples once and then answers by a function. Candidates for
  `RandomSystems.Converter.ProgramAttachment`.
* `Interface.Resource.sample_fTransform`, `Interface.Resource.smul_sample` and
  `Interface.Resource.ofFunction_eq_ofDeterministic`, from `cbc-mac-cc`,
  `CBCMAC/Upstream/Resource.lean`: sampling along a map, attaching to a sampled resource, and a
  function as a deterministic resource. Candidates for `ConstructiveCryptography.Functional`.
* `Interface.ofDDC_ofProgramOn_smul_ofFunction`, from `cbc-mac-cc`,
  `CBCMAC/Upstream/Resource.lean`: the converter of a program on a function. Candidate for
  `ConstructiveCryptography.DSL.Converters`, beside `ofDDC_ofProgramOn_smul_ofAutomaton`.
* `Interface.Resource.sample_uniform_equiv`, `Interface.Resource.sample_sample`,
  `Interface.Resource.sample_comm`, `Interface.Resource.sample_congr_law`,
  `Interface.Resource.sample_eq_sample_of_fTransform`,
  `Interface.Resource.sample_eq_sample_of_fTransform_support`,
  `Interface.Resource.eq_of_not_domain` and `Interface.Resource.sample_ofFunction_apply`: a
  uniform sample along a bijection, two samples as one of the pair, independent samples in either
  order, samples related by a map, also on the possible samples only, the resources of an
  interface without histories, and a sampled function on a transcript.
  Candidates for `ConstructiveCryptography.Functional`.
* `Interface.Resource.ofFunction_eq_ofAutomaton`, `Interface.Resource.ofAutomaton_eq_sample`,
  `Interface.Resource.ofAutomaton_fTransform` and
  `Interface.Resource.ofAutomaton_single_congr_on_domain`: a function as an automaton, an
  automaton as a sample of its initial states, and automata agreeing on the domain. Candidates
  for `ConstructiveCryptography.Functional`, beside `Resource.ofAutomaton`.
* `Interface.Converter.ofPreservingProgram_smul_ofFunction`, `sourceEntry`,
  `Interface.ofDDC_ofProgramOn_source_smul_ofFunction`,
  `Interface.Converter.ofPreservingProgram_source_smul_ofFunction` and
  `Interface.Converter.ofProgram_smul_ofAutomaton_eq_sample`: a program on a function, beside a
  source and on a function, and on an automaton that is a function at each sample. Candidates
  for `ConstructiveCryptography.DSL.Converters`, beside `ofPreservingProgram_smul_ofAutomaton`.
* `Interface.Converter.ofProgramPerPort`: a bounded program typed by per-port budgets, every
  inside label at `b` times a bound on the total outside budget. It types by per-port budgets
  the components that make several inside calls per invocation, which the DSL types by a total
  budget only. Candidate for `ConstructiveCryptography.DSL.Converters`.
* `List.find?_finRange_val`: the first index of a value in `List.finRange n`. Candidate for
  Mathlib, `Mathlib.Data.List.FinRange`.

## Main definitions

* `functionSystem g`: the system of the function `g`
* `Program.answer P g s o u n h`: an invocation run against `g`
* `sourceEntry law t c`: the `c`-th entry a source reads from its table `t`
* `Interface.Converter.ofProgramPerPort s P hb q n hn`: a bounded program at per-port budgets

## Main results

* `Program.feed_function`, `Program.inline_function`: the program attached to the system of `g`
* `Program.trim_apply_ofProgramOn_function`: the same on domains
* `functionSystem_eq_automatonSystem`, `automatonSystem_of_stored`: functions as automata
* `Interface.Resource.sample_fTransform`, `Interface.Resource.smul_sample`
* `Interface.Resource.sample_uniform_equiv`, `Interface.Resource.sample_sample`,
  `Interface.Resource.sample_comm`, `Interface.Resource.sample_eq_sample_of_fTransform`,
  `Interface.Resource.sample_eq_sample_of_fTransform_support`
* `Interface.Resource.sample_ofFunction_apply`: a sampled function gives a transcript the
  probability that it answers the transcript
* `Interface.Resource.ofFunction_eq_ofDeterministic`, `Interface.Resource.ofFunction_eq_ofAutomaton`
* `Interface.Resource.ofAutomaton_eq_sample`, `Interface.Resource.ofAutomaton_fTransform`,
  `Interface.Resource.ofAutomaton_single_congr_on_domain`: automata as samples
* `Interface.ofDDC_ofProgramOn_smul_ofFunction`,
  `Interface.Converter.ofPreservingProgram_smul_ofFunction`: a program on a function
* `Interface.ofDDC_ofProgramOn_source_smul_ofFunction`,
  `Interface.Converter.ofPreservingProgram_source_smul_ofFunction`,
  `Interface.Converter.ofProgram_smul_ofAutomaton_eq_sample`: sampling programs on functions, and
  programs on sampled automata, as sampled functions
-/

namespace SystemAlgebra

open Classical

variable {S O J : Type} {U V : O → Type} {X Y : J → Type}

/-- **The first index of a value** in `List.finRange n` is that value, when it is below `n`. -/
lemma _root_.List.find?_finRange_val (n c : ℕ) :
    (List.finRange n).find? (fun k => decide (k.val = c)) =
      if h : c < n then some ⟨c, h⟩ else none := by
  split_ifs with h
  · rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simp, c, by simp [h], by simp, fun j hj => ?_⟩
    simp only [List.getElem_finRange, Fin.cast_mk, Bool.not_eq_true', decide_eq_false_iff_not]
    omega
  · rw [List.find?_eq_none]
    intro k _
    simp only [decide_eq_true_eq]
    omega

/-- **The system of the function `g`**: it answers each nonempty history with `g` at its last
query. Restated from `cbc-mac-cc`, `CBCMAC/Upstream/ProgramAttachment.lean`. -/
def functionSystem (g : ∀ j, X j → Y j) : InterfaceSystem J X Y := fun h =>
  (h.getLast?.map fun x => (⟨x.1, g x.1 x.2⟩ : Σ j, Y j) : Part _)

@[simp] lemma functionSystem_snoc (g : ∀ j, X j → Y j) (h : List (Σ j, X j)) (x : Σ j, X j) :
    functionSystem g (h ++ [x]) = Part.some ⟨x.1, g x.1 x.2⟩ := by
  simp [functionSystem]

lemma functionSystem_dom (g : ∀ j, X j → Y j) (h : List (Σ j, X j)) :
    (functionSystem g h).Dom ↔ h ≠ [] := by
  rcases List.eq_nil_or_concat h with rfl | ⟨h, x, rfl⟩
  · simp [functionSystem]
  · simp [List.concat_eq_append]

lemma functionSystem_isDDS (g : ∀ j, X j → Y j) : IsDDS (functionSystem g) :=
  ⟨by simp [SilentAtEmpty, functionSystem], fun p _ _ hne _ => (functionSystem_dom g p).mpr hne⟩

lemma functionSystem_replies (g : ∀ j, X j → Y j) :
    RepliesAtQueriedInterface (functionSystem g) := by
  intro h a y hy
  rw [functionSystem_snoc] at hy
  obtain rfl := Part.mem_some_iff.mp hy
  rfl

/-- **The system of a function is an automaton** with a single state. -/
lemma functionSystem_eq_automatonSystem (g : ∀ j, X j → Y j) :
    functionSystem g = automatonSystem (fun (_ : Unit) j x => ((), g j x)) () := by
  funext h
  rcases List.eq_nil_or_concat h with rfl | ⟨h, x, rfl⟩
  · simp [functionSystem]
  · rw [List.concat_eq_append, functionSystem_snoc, automatonSystem_snoc]

/-- **An automaton that samples once** and then answers by a function: if, from `(none, r₀)`, an
input stores `k` and is answered by `f k`, and from a state storing `k` every input keeps it and
is answered by `f k`, the automaton is the function `f k`. -/
lemma automatonSystem_of_stored {K R : Type}
    (step : Option K × R → (j : J) → X j → (Option K × R) × Y j) (f : K → ∀ j, X j → Y j)
    (r₀ : R) (k : K) (first : ∀ j x, ∃ r, step (none, r₀) j x = ((some k, r), f k j x))
    (later : ∀ r j x, ∃ r', step (some k, r) j x = ((some k, r'), f k j x)) :
    automatonSystem step (none, r₀) = functionSystem (f k) := by
  rw [functionSystem_eq_automatonSystem]
  refine automatonSystem_eq_of_bisim _ (rel := fun st _ => st = (none, r₀) ∨ st.1 = some k)
    ?_ (Or.inl rfl)
  rintro ⟨st, r⟩ ⟨⟩ j x h
  rcases h with h | h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    obtain ⟨r', hr⟩ := first j x
    rw [hr]
    exact ⟨rfl, Or.inr rfl⟩
  · dsimp only at h
    subst h
    obtain ⟨r', hr⟩ := later r j x
    rw [hr]
    exact ⟨rfl, Or.inr rfl⟩

namespace Program

/-- **An invocation run against the function `g`**: the body runs from the exchanges `h`, each
inside query answered by its value under `g`, with at most `n` more of them. Restated from
`cbc-mac-cc`, `CBCMAC/Upstream/ProgramAttachment.lean`. -/
def answer (P : Program S O J U V X Y) (g : ∀ j, X j → Y j) (s : S) (o : O) (u : U o) :
    ℕ → List ((Σ j, X j) × (Σ j, Y j)) → Option (S × V o)
  | 0, h => (P s o u h).elim some fun _ => none
  | n + 1, h =>
    match P s o u h with
    | .inl a => some a
    | .inr q => answer P g s o u n (h ++ [(q, ⟨q.1, g q.1 q.2⟩)])

variable {P : Program S O J U V X Y}

variable (P) in
/-- **An invocation fed by the system of a function is the invocation run against it.**
Restated from `cbc-mac-cc`, `CBCMAC/Upstream/ProgramAttachment.lean`. -/
lemma feed_function (g : ∀ j, X j → Y j) :
    ∀ (n : ℕ) (s : S) (o : O) (u : U o) (h : List ((Σ j, X j) × (Σ j, Y j)))
      (rh : List (Σ j, X j)) (m : Mode S O J U X Y) (x : Σ l, twoFam U Y l),
      P.step m x = some (P.emit s o u h) →
      (P.feed (functionSystem g) (n + 1) m x rh).map (fun t => (t.1, t.2.2)) =
        (P.answer g s o u n h).map (fun a => (.idle a.1, ⟨o, a.2⟩)) := by
  intro n
  induction n with
  | zero =>
    intro s o u h rh m x hs
    rw [feed, hs]
    cases hq : P s o u h with
    | inl a => simp [emit, hq, answer]
    | inr q =>
      simp only [emit, hq]
      simp [feed, answer, hq]
  | succ n ih =>
    intro s o u h rh m x hs
    rw [feed, hs]
    cases hq : P s o u h with
    | inl a => simp [emit, hq, answer]
    | inr q =>
      simp only [emit, hq]
      have hd : (functionSystem g (rh ++ [⟨q.1, q.2⟩])).Dom :=
        (functionSystem_dom g _).mpr (by simp)
      rw [dif_pos hd]
      have hget : (functionSystem g (rh ++ [⟨q.1, q.2⟩])).get hd = ⟨q.1, g q.1 q.2⟩ := by
        simp
      rw [hget]
      dsimp only
      refine (ih s o u (h ++ [(q, ⟨q.1, g q.1 q.2⟩)]) (rh ++ [⟨q.1, q.2⟩]) (.busy o s u h q)
        ⟨⟨some (), q.1⟩, g q.1 q.2⟩ (by simp [step])).trans ?_
      simp only [answer, hq]

variable (P) in
/-- **A program attached to the system of a function**: if, against `g`, every invocation on `u`
returns `f u` from every state, the inlined program is the system of `f`. Restated from
`cbc-mac-cc`, `CBCMAC/Upstream/ProgramAttachment.lean`. -/
lemma inline_function {b : ℕ} (g : ∀ j, X j → Y j) (f : ∀ o, U o → V o) (s : S)
    (answers : ∀ t o u, ∃ t', P.answer g t o u b [] = some (t', f o u)) :
    P.inline (functionSystem g) b s = functionSystem f := by
  have after : ∀ us : List (Σ o, U o),
      ∃ t rh, P.inlineAfter (functionSystem g) b s us = some (.idle t, rh) := by
    intro us
    induction us using List.reverseRecOn with
    | nil => exact ⟨s, [], rfl⟩
    | append_singleton us a ih =>
      obtain ⟨t, rh, hst⟩ := ih
      obtain ⟨t', ht'⟩ := answers t a.1 a.2
      have hf := P.feed_function g b t a.1 a.2 [] rh (.idle t) ⟨⟨none, a.1⟩, a.2⟩ rfl
      rw [ht'] at hf
      obtain ⟨⟨m', rh', w⟩, hfeed, heq⟩ := Option.map_eq_some_iff.mp hf
      simp only [Prod.mk.injEq] at heq
      refine ⟨t', rh', ?_⟩
      rw [inlineAfter_snoc, hst, Option.bind_some, hfeed, Option.map_some, heq.1]
  funext us
  rcases List.eq_nil_or_concat us with rfl | ⟨us, a, rfl⟩
  · simp [inline, functionSystem]
  rw [List.concat_eq_append, inline_snoc, functionSystem_snoc]
  obtain ⟨t, rh, hst⟩ := after us
  obtain ⟨t', ht'⟩ := answers t a.1 a.2
  have hf := P.feed_function g b t a.1 a.2 [] rh (.idle t) ⟨⟨none, a.1⟩, a.2⟩ rfl
  rw [ht'] at hf
  obtain ⟨⟨m', rh', w⟩, hfeed, heq⟩ := Option.map_eq_some_iff.mp hf
  simp only [Prod.mk.injEq] at heq
  rw [hst, Option.bind_some, hfeed, Option.map_some, heq.2]
  rfl

/-- **A program on the outside domain `F` attached to a function on the inside domain `E`** is
the function the program computes, on `F`, when the program is a DDC from `E`. Restated from
`cbc-mac-cc`, `CBCMAC/Upstream/ProgramAttachment.lean`. -/
lemma trim_apply_ofProgramOn_function {b : ℕ} (hP : P.Bounded b) (g : ∀ j, X j → Y j)
    (f : ∀ o, U o → V o) (s : S)
    (answers : ∀ t o u, ∃ t', P.answer g t o u b [] = some (t', f o u))
    {E : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop}
    (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (hα : IsDDCFrom E F b (DDC.ofProgramOn s P F)) :
    trim (apply (DDC.ofProgramOn s P F) (filterDom E (functionSystem g))) =
      filterDom F (functionSystem f) := by
  have hsub : ∀ h y, y ∈ filterDom E (functionSystem g) h → y ∈ functionSystem g h :=
    fun h y hy => ((filterDom_mem_iff E _ h y).mp hy).2
  have hdomE : ∀ h, (filterDom E (functionSystem g) h).Dom ↔ E h := by
    intro h
    rw [filterDom_dom, functionSystem_dom]
    exact ⟨fun hd => hd.1, fun hd => ⟨hd, fun he => hE.1 (he ▸ hd)⟩⟩
  obtain ⟨-, hdom⟩ := hα.mapsDomain hF _ ((functionSystem_isDDS g).filterDom E hE.2)
    (fun h x y hy => functionSystem_replies g h x y (hsub _ _ hy)) hdomE
  have hfull : trim (apply (DDC.ofProgramOn s P F) (functionSystem g)) =
      filterDom F (functionSystem f) := by
    rw [trim_apply_ofProgramOn s hP F hF.2, inline_function P g f s answers]
  rw [← hfull]
  apply IsDDS.eq_of_replies_iff (SilentAtEmpty.isDDS_trim (by simp [SilentAtEmpty, apply_eq]))
    (SilentAtEmpty.isDDS_trim (by simp [SilentAtEmpty, apply_eq]))
  apply replies_iff_of_dom_iff
  · intro h
    rw [hdom, hfull, filterDom_dom, functionSystem_dom]
    exact ⟨fun hd => ⟨hd, fun he => hF.1 (he ▸ hd)⟩, fun hd => hd.1⟩
  · intro xs ys hr
    rw [replies_trim_iff, apply_eq] at hr ⊢
    exact hr.interconnect_mono (pair_mono (fun _ _ h => h) hsub)

end Program

namespace Interface

open Probability CategoryTheory

variable {A : Interface}

/-- **Sampling along a map** samples the composite. Restated from `cbc-mac-cc`,
`CBCMAC/Upstream/Resource.lean`. -/
lemma Resource.sample_fTransform {K K' : Type} (φ : K → K') (P : Probability.Distribution K)
    [Probability.Distribution.IsProbability P] (R : K' → Resource A) :
    Resource.sample (Probability.Distribution.fTransform φ P) R =
      Resource.sample P (fun k => R (φ k)) := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [Resource.sample_mass, Resource.sample_mass]
  exact Distribution.sum_fTransform_mul φ P (fun k => (R k).1 h)

/-- **Attaching to a sampled resource** attaches to each sample. Restated from `cbc-mac-cc`,
`CBCMAC/Upstream/Resource.lean`. -/
lemma Resource.smul_sample {B : Interface} (α : A ⟶ B) {K : Type}
    (P : Probability.Distribution K) [Probability.Distribution.IsProbability P]
    (R : K → Resource B) :
    α • Resource.sample P R = Resource.sample P (fun k => α • R k) := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [Resource.sample_mass]
  change (RandomSystem.parallel α.1 (RandomSystem.mix _ fun k => (R k).1)).connectionLaw
    resourceRoute resourceInput (h.map Prod.fst) _ (h.map Prod.snd) = _
  rw [RandomSystem.parallel_mix_right, RandomSystem.connectionLaw_mix]
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rfl

/-- **A function is a deterministic resource**: the system of the function on the interface's
domain. Restated from `cbc-mac-cc`, `CBCMAC/Upstream/Resource.lean`. -/
lemma Resource.ofFunction_eq_ofDeterministic (g : ∀ i, A.X i → A.Y i) :
    Resource.ofFunction g = ofDeterministic (filterDom A.domain (functionSystem g))
      ⟨(functionSystem_isDDS g).filterDom _ A.nonempty_prefix.2,
        fun h x y hy => functionSystem_replies g h x y ((filterDom_mem_iff _ _ _ _).mp hy).2,
        fun h => by
          rw [filterDom_dom, functionSystem_dom]
          exact ⟨fun hd => hd.1, fun hd => ⟨hd, fun he => A.nonempty_prefix.1 (he ▸ hd)⟩⟩⟩ := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  have replies : h.map Prod.snd = (h.map Prod.fst).map (fun x => ⟨x.1, g x.1 x.2⟩) ↔
      ∀ z ∈ h, z.2 = ⟨z.1.1, g z.1.1 z.1.2⟩ := by
    rw [List.map_map, List.map_eq_map_iff]
    rfl
  have evaluator : filterDom A.domain (functionSystem g) =
      (DDS.ofFunction A.domain A.nonempty_prefix (fun x => ⟨x.1, g x.1 x.2⟩)).1 := rfl
  rw [Resource.ofFunction_mass, ofDeterministic_mass, evaluator, DDS.replies_ofFunction_iff,
    replies, List.map_eq_nil_iff]
  congr 1

/-- **The converter of a program on a function**: if, against `g`, every invocation on `u`
returns `f u` from every state, attaching the program's converter to the function `g` gives the
function `f`. Restated from `cbc-mac-cc`, `CBCMAC/Upstream/Resource.lean`. -/
lemma ofDDC_ofProgramOn_smul_ofFunction {B : Interface} {S : Type} (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    (hα : IsDDCFrom B.domain A.domain b (DDC.ofProgramOn s P A.domain))
    (g : ∀ j, B.X j → B.Y j) (f : ∀ o, A.X o → A.Y o)
    (answers : ∀ t o u, ∃ t', P.answer g t o u b [] = some (t', f o u)) :
    Interface.ofDDC (DDC.ofProgramOn s P A.domain) hα • Resource.ofFunction g =
      Resource.ofFunction f := by
  rw [Resource.ofFunction_eq_ofDeterministic g, Resource.ofFunction_eq_ofDeterministic f]
  apply Subtype.ext
  apply RandomSystem.ext
  intro t
  rw [ofDeterministic, ofDDC_ofProgramOn_smul_ofPDS s P hb hα, Distribution.mass_single,
    ← Program.trim_apply_ofProgramOn s hb A.domain A.nonempty_prefix.2,
    Program.trim_apply_ofProgramOn_function hb g f s answers B.nonempty_prefix A.nonempty_prefix
      hα, ofDeterministic_mass]

/-- **Sampling uniformly along a bijection** samples the composite: a uniform `k'` is `e k` for a
uniform `k`. -/
lemma Resource.sample_uniform_equiv {K K' : Type} [Fintype K] [Nonempty K] [Fintype K']
    [Nonempty K'] (e : K ≃ K') (R : K' → Resource A) :
    Resource.sample (Distribution.uniform K') R =
      Resource.sample (Distribution.uniform K) (fun k => R (e k)) := by
  refine Eq.trans ?_ (Resource.sample_fTransform e (Distribution.uniform K) R)
  congr 1
  exact (Distribution.fTransform_equiv_uniform e).symm

/-- **Sampling twice** is sampling the independent pair. -/
lemma Resource.sample_sample {K L : Type} (P : Distribution K) [Distribution.IsProbability P]
    (Q : Distribution L) [Distribution.IsProbability Q] (R : K → L → Resource A) :
    Resource.sample P (fun k => Resource.sample Q (R k)) =
      Resource.sample (Distribution.prod P Q) (fun kl => R kl.1 kl.2) := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  simp only [Resource.sample_mass]
  exact (Distribution.sum_prod_mul P Q (fun kl => (R kl.1 kl.2).1 h)).symm

/-- **Independent samples commute**: sampling `k` then `l` is sampling `l` then `k`. -/
lemma Resource.sample_comm {K L : Type} (P : Distribution K) [Distribution.IsProbability P]
    (Q : Distribution L) [Distribution.IsProbability Q] (R : K → L → Resource A) :
    Resource.sample P (fun k => Resource.sample Q (R k)) =
      Resource.sample Q (fun l => Resource.sample P (fun k => R k l)) := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  simp only [Resource.sample_mass, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _

/-- A history admitted by an interface makes its bound positive. -/
lemma bound_pos_of_domain {h : List (Σ i, A.X i)} (hd : A.domain h) : 0 < A.bound :=
  lt_of_lt_of_le (List.length_pos_of_ne_nil fun he => A.nonempty_prefix.1 (he ▸ hd))
    (A.length_le h hd)

/-- **Resources on an interface admitting no history** are equal. -/
lemma Resource.eq_of_not_domain {R S : Resource A} (empty : ∀ h, ¬ A.domain h) : R = S := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rcases List.eq_nil_or_concat h with rfl | ⟨h, z, rfl⟩
  · rw [RandomSystem.mass_nil, RandomSystem.mass_nil]
  · rw [List.concat_eq_append, R.1.mass_eq_zero_of_not_admitted (empty _),
      S.1.mass_eq_zero_of_not_admitted (empty _)]

/-- Sampling from equal laws. -/
lemma Resource.sample_congr_law {K : Type} {P P' : Distribution K}
    [Distribution.IsProbability P] [Distribution.IsProbability P'] (h : P = P')
    (R : K → Resource A) : Resource.sample P R = Resource.sample P' R := by
  subst h
  rfl

/-- **Samples related by a map**: sampling `RP k` for `k ← P` is sampling `RQ l` for `l ← Q`, if `Q`
is `P` pushed along `φ` and `RP k = RQ (φ k)`. -/
lemma Resource.sample_eq_sample_of_fTransform {K L : Type} (P : Distribution K)
    [Distribution.IsProbability P] (Q : Distribution L) [Distribution.IsProbability Q] (φ : K → L)
    (RP : K → Resource A) (RQ : L → Resource A) (hlaw : Distribution.fTransform φ P = Q)
    (h : ∀ k, RP k = RQ (φ k)) : Resource.sample P RP = Resource.sample Q RQ := by
  rw [show RP = fun k => RQ (φ k) from funext h, ← Resource.sample_fTransform]
  exact Resource.sample_congr_law hlaw _

/-- **Samples related by a map on the possible samples**: sampling `RP k` for `k ← P` is sampling
`RQ l` for `l ← Q`, if `Q` is `P` pushed along `φ` and `RP k = RQ (φ k)` for every possible `k`. -/
lemma Resource.sample_eq_sample_of_fTransform_support {K L : Type} (P : Distribution K)
    [Distribution.IsProbability P] (Q : Distribution L) [Distribution.IsProbability Q] (φ : K → L)
    (RP : K → Resource A) (RQ : L → Resource A) (hlaw : Distribution.fTransform φ P = Q)
    (h : ∀ k ∈ P.support, RP k = RQ (φ k)) : Resource.sample P RP = Resource.sample Q RQ := by
  refine Eq.trans ?_ (Resource.sample_eq_sample_of_fTransform P Q φ (fun k => RQ (φ k)) RQ hlaw
    fun _ => rfl)
  apply Subtype.ext
  apply RandomSystem.ext
  intro t
  rw [Resource.sample_mass, Resource.sample_mass]
  exact Finset.sum_congr rfl fun k hk => by rw [h k hk]

/-- **A sampled function on a transcript**: the probability of the transcript `h` is the
probability that the sampled function answers it, `h` being admitted and each reply the value of
the function at its query. -/
lemma Resource.sample_ofFunction_apply {K : Type} (P : Distribution K)
    [Distribution.IsProbability P] (f : K → ∀ i, A.X i → A.Y i)
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) :
    (Resource.sample P fun k => Resource.ofFunction (f k)).1 h =
      P.mass fun k => (h = [] ∨ A.domain (h.map Prod.fst)) ∧
        ∀ z ∈ h, z.2 = ⟨z.1.1, f k z.1.1 z.1.2⟩ := by
  classical
  -- A sampled resource gives `h` the average over the samples of their probability of `h`, ...
  rw [Resource.sample_mass]
  unfold Distribution.mass Finsupp.sum
  refine Finset.sum_congr rfl fun k _ => ?_
  -- (Applying the summands to the sample `k`.)
  dsimp only
  -- ... and a function gives `h` probability `1` if it answers `h`, and `0` otherwise.
  rw [Resource.ofFunction_mass]
  by_cases answered : (h = [] ∨ A.domain (h.map Prod.fst)) ∧
      ∀ z ∈ h, z.2 = ⟨z.1.1, f k z.1.1 z.1.2⟩
  · -- `f k` answers `h`: `P k · 1 = P k`.
    rw [if_pos answered, if_pos answered, mul_one]
  · -- `f k` does not answer `h`: `P k · 0 = 0`.
    rw [if_neg answered, if_neg answered, mul_zero]

/-- **A function is an automaton** with a single state. -/
lemma Resource.ofFunction_eq_ofAutomaton (g : ∀ i, A.X i → A.Y i) :
    Resource.ofFunction g = Resource.ofAutomaton A (fun (_ : Unit) i x => ((), g i x))
      (Distribution.ProbDist.single ()) := by
  rw [Resource.ofFunction_eq_ofDeterministic]
  apply Subtype.ext
  apply RandomSystem.ext
  intro t
  rw [ofDeterministic_mass, Resource.ofAutomaton_mass]
  change _ = Distribution.mass (Finsupp.single () 1 : Distribution Unit) _
  rw [Distribution.mass_single, functionSystem_eq_automatonSystem]

/-- **An automaton that is a function at each initial state** is the sampled function. -/
lemma Resource.ofAutomaton_eq_sample {S K : Type} (step : S → (i : A.I) → A.X i → S × A.Y i)
    (P : Distribution K) [Distribution.IsProbability P] (init : K → S)
    (f : K → ∀ i, A.X i → A.Y i) (h : ∀ k, automatonSystem step (init k) = functionSystem (f k)) :
    Resource.ofAutomaton A step ⟨Distribution.fTransform init P,
        Distribution.fTransform_isProbDist _ (Distribution.IsProbability.isProbDist P)⟩ =
      Resource.sample P (fun k => Resource.ofFunction (f k)) := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro t
  rw [Resource.ofAutomaton_mass, Resource.sample_ofFunction_mass, behaviorMass,
    Distribution.mass_fTransform, Distribution.mass_fTransform]
  refine Distribution.mass_congr _ fun k => ?_
  rw [h k]
  rfl

/-- **An automaton with a sampled initial state** samples the automaton started there. -/
lemma Resource.ofAutomaton_fTransform {S K : Type} (step : S → (i : A.I) → A.X i → S × A.Y i)
    (P : Distribution K) [Distribution.IsProbability P] (init : K → S) :
    Resource.ofAutomaton A step ⟨Distribution.fTransform init P,
        Distribution.fTransform_isProbDist _ (Distribution.IsProbability.isProbDist P)⟩ =
      Resource.sample P
        (fun k => Resource.ofAutomaton A step (Distribution.ProbDist.single (init k))) := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro t
  rw [Resource.ofAutomaton_mass, Resource.sample_mass, Distribution.mass_fTransform]
  unfold Distribution.mass
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Resource.ofAutomaton_mass]
  change _ = P k * Distribution.mass (Finsupp.single (init k) 1) _
  rw [Distribution.mass_single]
  split_ifs <;> simp

/-- **Automata agreeing on the domain**: started in related states, if every admitted input
keeps the states related and is answered alike, the automata are the same resource. -/
lemma Resource.ofAutomaton_single_congr_on_domain {S S' : Type}
    {step : S → (i : A.I) → A.X i → S × A.Y i} {step' : S' → (i : A.I) → A.X i → S' × A.Y i}
    {s : S} {s' : S'} (rel : List (Σ i, A.X i) → S → S' → Prop) (h₀ : rel [] s s')
    (hstep : ∀ h x a a', A.domain (h ++ [x]) → rel h a a' →
      (step a x.1 x.2).2 = (step' a' x.1 x.2).2 ∧
        rel (h ++ [x]) (step a x.1 x.2).1 (step' a' x.1 x.2).1) :
    Resource.ofAutomaton A step (Distribution.ProbDist.single s) =
      Resource.ofAutomaton A step' (Distribution.ProbDist.single s') := by
  have states : ∀ h : List (Σ i, A.X i), (h = [] ∨ A.domain h) →
      rel h (stateAfter step s h) (stateAfter step' s' h) := by
    intro h
    induction h using List.reverseRecOn with
    | nil => intro _; exact h₀
    | append_singleton h x ih =>
      intro hd
      have hd : A.domain (h ++ [x]) := hd.resolve_left (by simp)
      have hh : h = [] ∨ A.domain h := by
        by_cases hn : h = []
        · exact Or.inl hn
        · exact Or.inr (A.nonempty_prefix.2 (List.prefix_append _ _) hn hd)
      rw [stateAfter_snoc, stateAfter_snoc]
      exact (hstep _ _ _ _ hd (ih hh)).2
  have systems : filterDom A.domain (automatonSystem step s) =
      filterDom A.domain (automatonSystem step' s') := by
    funext h
    unfold filterDom
    split_ifs with hd
    · rcases List.eq_nil_or_concat h with rfl | ⟨h, x, rfl⟩
      · rfl
      · rw [List.concat_eq_append] at hd ⊢
        have hh : h = [] ∨ A.domain h := by
          by_cases hn : h = []
          · exact Or.inl hn
          · exact Or.inr (A.nonempty_prefix.2 (List.prefix_append _ _) hn hd)
        rw [automatonSystem_snoc, automatonSystem_snoc, (hstep _ _ _ _ hd (states h hh)).1]
    · rfl
  apply Subtype.ext
  apply RandomSystem.ext
  intro t
  rw [Resource.ofAutomaton_mass, Resource.ofAutomaton_mass]
  change Distribution.mass (Finsupp.single s 1) _ = Distribution.mass (Finsupp.single s' 1) _
  rw [Distribution.mass_single, Distribution.mass_single, systems]

/-- **A port-preserving program attached to a function** is the program's automaton against the
function. -/
lemma Converter.ofPreservingProgram_smul_ofFunction {B : Interface} {S : Type} (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b) (ι : A.I → Option B.I)
    (hι : P.PortPreserving ι) (q : A.I → ℕ)
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) → B.domain ys)
    (g : ∀ j, B.X j → B.Y j) :
    Converter.ofPreservingProgram s P hb ι hι q hA hB • Resource.ofFunction g =
      Resource.ofAutomaton A (P.combine (fun (_ : Unit) j x => ((), g j x)) hb)
        (Distribution.ProbDist.single (s, ())) := by
  rw [Resource.ofFunction_eq_ofAutomaton, Converter.ofPreservingProgram_smul_ofAutomaton]
  congr 1
  exact Subtype.ext Finsupp.mapDomain_single

/-- The `c`-th entry a source reads from its table. -/
noncomputable def sourceEntry {Z : Type} {k : ℕ} (law : Distribution.ProbDist Z) (t : Fin k → Z)
    (c : ℕ) : Z :=
  (sourceStep law (t, c) () ()).2

/-- Reading a table along a cast of its length. -/
lemma sourceEntry_cast {Z : Type} [Fintype Z] {k k' : ℕ} (law : Distribution.ProbDist Z)
    (h : k = k') (t : Fin k → Z) (c : ℕ) :
    sourceEntry law (((finCongr h).arrowCongr (Equiv.refl Z)) t) c = sourceEntry law t c := by
  subst h
  rfl

/-- **The first entry of a source's table** has the source's law. -/
lemma sourceEntry_zero_law {Z : Type} [Fintype Z] {k : ℕ} (law : Distribution.ProbDist Z)
    (hk : 0 < k) :
    Distribution.fTransform (fun t : Fin k → Z => sourceEntry law t 0)
      (Distribution.pi fun _ => law.1) = law.1 := by
  have first : (fun t : Fin k → Z => sourceEntry law t 0) = fun t => t ⟨0, hk⟩ := by
    funext t
    simp only [sourceEntry, sourceStep]
    rw [dif_pos hk]
  rw [first]
  change Distribution.marginalAt _ _ = _
  rw [Distribution.marginalAt_pi]
  simp [law.2.2]

/-- **A program beside a source, attached to a function**: if, against the function `g` and a
source table `t`, the program started in `s` is the function `f z` of the entry `z` it reads at
the table's position, the converter of the program beside the source of `law`, attached to `g`,
is the function `f z` for `z ← law`. The source is read at the first invocation; the table has
an entry when the interface admits a history. -/
lemma ofDDC_ofProgramOn_source_smul_ofFunction {B : Interface} {S Z : Type} [Fintype Z]
    {k : ℕ} (s : S)
    (P : Program S A.I (B.tensor (Interface.source Z k)).I A.X A.Y
      (B.tensor (Interface.source Z k)).X (B.tensor (Interface.source Z k)).Y) {b : ℕ}
    (hb : P.Bounded b)
    (hα : IsDDCFrom (B.tensor (Interface.source Z k)).domain A.domain b
      (DDC.ofProgramOn s P A.domain))
    (law : Distribution.ProbDist Z) (g : ∀ j, B.X j → B.Y j) (f : Z → ∀ i, A.X i → A.Y i)
    (answers : ∀ (t : Fin k → Z) c, automatonSystem (P.combine (parallelStep
      (fun (_ : Unit) j x => ((), g j x)) (sourceStep (q := k) law)) hb) (s, ((), (t, c))) =
        functionSystem (f (sourceEntry law t c)))
    (admitted : ∀ h, A.domain h → 0 < k) :
    (Interface.ofDDC (DDC.ofProgramOn s P A.domain) hα ≫
        rightContext B (Resource.source law k)) • Resource.ofFunction g =
      Resource.sample law.1 (fun z => Resource.ofFunction (f z)) := by
  rw [Interface.comp_smul, attach_rightContext, Resource.source,
    Resource.ofFunction_eq_ofAutomaton, parallel_ofAutomaton,
    Interface.ofDDC_ofProgramOn_smul_ofAutomaton s P hb]
  erw [Resource.ofAutomaton_eq_sample _ _ _ (fun r => f (sourceEntry law r.2.1 r.2.2))
    fun r => answers r.2.1 r.2.2]
  -- The sample is the first entry of the table, unless no history is admitted.
  rw [Resource.sample_congr_law (P' := Distribution.fTransform (fun t => ((), (t, 0)))
      (Distribution.pi fun _ => law.1)) (by
        change Distribution.prod (Finsupp.single () 1) _ = _
        rw [Distribution.prod_single_left, Distribution.fTransform_comp]
        rfl),
    Resource.sample_fTransform]
  refine (Resource.sample_fTransform (fun t => sourceEntry law t 0) _
    (fun z => Resource.ofFunction (f z))).symm.trans ?_
  by_cases hk : 0 < k
  · exact Resource.sample_congr_law (sourceEntry_zero_law law hk) _
  · exact Resource.eq_of_not_domain fun h hd => hk (admitted h hd)

/-- **A port-preserving program beside a source, attached to a function**: the converter of the
program, as `ofDDC_ofProgramOn_source_smul_ofFunction`. -/
lemma Converter.ofPreservingProgram_source_smul_ofFunction {B : Interface} {S Z : Type}
    [Fintype Z] {k : ℕ} (s : S)
    (P : Program S A.I (B.tensor (Interface.source Z k)).I A.X A.Y
      (B.tensor (Interface.source Z k)).X (B.tensor (Interface.source Z k)).Y) {b : ℕ}
    (hb : P.Bounded b) (ι : A.I → Option (B.tensor (Interface.source Z k)).I)
    (hι : P.PortPreserving ι) (q : A.I → ℕ)
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) →
        (B.tensor (Interface.source Z k)).domain ys)
    (law : Distribution.ProbDist Z) (g : ∀ j, B.X j → B.Y j) (f : Z → ∀ i, A.X i → A.Y i)
    (answers : ∀ (t : Fin k → Z) c, automatonSystem (P.combine (parallelStep
      (fun (_ : Unit) j x => ((), g j x)) (sourceStep (q := k) law)) hb) (s, ((), (t, c))) =
        functionSystem (f (sourceEntry law t c)))
    (admitted : ∀ h, A.domain h → 0 < k) :
    (Converter.ofPreservingProgram s P hb ι hι q hA hB ≫ rightContext B (Resource.source law k)) •
        Resource.ofFunction g =
      Resource.sample law.1 (fun z => Resource.ofFunction (f z)) :=
  ofDDC_ofProgramOn_source_smul_ofFunction s P hb _ law g f answers admitted

/-- **A program attached to an automaton that is a function at each sample**: if the program
started in `s`, against the automaton started in `init k`, is the function `f k`, the converter
of the program attached to the automaton with initial states `init k` for `k ← L` is the
function `f k` for `k ← L`. -/
lemma Converter.ofProgram_smul_ofAutomaton_eq_sample {B : Interface} {S R K : Type} (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    (hB : ∀ xs, xs ≠ [] → xs.length ≤ b * A.bound → B.domain xs)
    (stepR : R → (j : B.I) → B.X j → R × B.Y j) (initial : Distribution.ProbDist R)
    (L : Distribution K) [Distribution.IsProbability L] (init : K → R)
    (hinit : initial.1 = Distribution.fTransform init L) (f : K → ∀ i, A.X i → A.Y i)
    (answers : ∀ k, automatonSystem (P.combine stepR hb) (s, init k) = functionSystem (f k)) :
    Converter.ofProgram s P hb hB • Resource.ofAutomaton B stepR initial =
      Resource.sample L (fun k => Resource.ofFunction (f k)) := by
  rw [Converter.ofProgram_smul_ofAutomaton]
  have law : (⟨Distribution.fTransform (fun r => (s, r)) initial.1,
      Distribution.fTransform_isProbDist _ initial.2⟩ : Distribution.ProbDist (S × R)) =
      ⟨Distribution.fTransform (fun k => (s, init k)) L,
        Distribution.fTransform_isProbDist _ (Distribution.IsProbability.isProbDist L)⟩ :=
    Subtype.ext (by
      change Distribution.fTransform _ initial.1 = _
      rw [hinit, Distribution.fTransform_comp]
      rfl)
  rw [law]
  exact Resource.ofAutomaton_eq_sample _ L _ f answers

/-- **A bounded program at per-port budgets**: a program making at most `b` inside calls per
invocation, from the per-port budgets `q`, with `∑ q ≤ n`, into the per-port budget `b · n` at
every inside label. -/
noncomputable def Converter.ofProgramPerPort {S I J : Type} [Fintype I] [Fintype J]
    {X Y : I → Type} {U V : J → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    [∀ j, Fintype (U j)] [∀ j, Fintype (V j)] (s : S) (P : Program S I J X Y U V) {b : ℕ}
    (hb : P.Bounded b) (q : I → ℕ) (n : ℕ) (hn : ∑ i, q i ≤ n) :
    portBudget I X Y q ⟶ portBudget J U V (fun _ => b * n) :=
  Converter.ofProgram s P hb fun xs hne hlen => by
    refine ⟨hne, fun j => le_trans ?_ ((hlen.trans_eq rfl).trans (Nat.mul_le_mul_left b hn))⟩
    rw [length_eq_sum_restrict xs]
    exact Finset.single_le_sum (f := fun k => (SystemAlgebra.restrict k xs).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

end Interface

end SystemAlgebra
