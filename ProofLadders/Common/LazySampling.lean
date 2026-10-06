import ProofLadders.Common.Functional
import ProofLadders.Common.Probability

/-!
# Lazy sampling

A lazy random dictionary answers a query from the value stored at its key; at a key not queried
before, it reads the next entry of a table of independent samples of one law and stores it.
Lazy sampling: the dictionary on a sampled table is the eagerly sampled function, independent
samples of the law at every key, sampled once, each query answered at the sample of its key.

Per table the answers depend on the order of the queries, so the two are compared transcript by
transcript. On a transcript the dictionary on a table `t` answers like the function reading `t`
at the rank of each key among the keys of the transcript, in the order of their first queries;
the entries of a table of independent samples at distinct ranks, like the samples at distinct
keys, are independent samples of the law.

Upstream candidates: `List.firstOccurrences` and its lemmas for Mathlib, `Mathlib.Data.List`;
`sourceEntry_of_lt`, `lazyDictionary`, `stateAfter_lazyDictionary`, `lazyDictionary_replies`,
`Distribution.mass_pi_sourceEntry_idxOf`, `Interface.Resource.ofAutomaton_lazyDictionary_mass`,
`Interface.Resource.sample_lazyDictionary` and
`Interface.Resource.ofAutomaton_eq_sample_of_lazyDictionary` for
`ConstructiveCryptography.Functional`, beside `Resource.ofAutomaton`.

## Main definitions

* `List.firstOccurrences ks`: the distinct elements of `ks`, in the order of their first
  occurrence
* `Interface.lazyDictionary A law t key answer`: the lazy random dictionary on the table `t`

## Main results

* `Interface.Distribution.mass_pi_sourceEntry_idxOf`: a table of independent samples read at
  the ranks of distinct keys
* `Interface.Resource.ofAutomaton_lazyDictionary_mass`: on a transcript, the dictionary on a
  table is a function
* `Interface.Resource.sample_lazyDictionary`: lazy sampling, the dictionary on a sampled table is
  the sampled function
* `Interface.Resource.ofAutomaton_eq_sample_of_lazyDictionary`: an automaton started on a sampled
  table that answers like the dictionary is the sampled function
-/

namespace List

variable {K : Type*} [DecidableEq K]

/-- The distinct elements of a list, in the order of their first occurrence. -/
def firstOccurrences (ks : List K) : List K :=
  ks.foldl (fun D k => if k ∈ D then D else D ++ [k]) []

@[simp] lemma firstOccurrences_nil : firstOccurrences ([] : List K) = [] := rfl

lemma firstOccurrences_append_singleton (ks : List K) (k : K) :
    firstOccurrences (ks ++ [k]) =
      if k ∈ firstOccurrences ks then firstOccurrences ks else firstOccurrences ks ++ [k] := by
  unfold firstOccurrences
  rw [foldl_append]
  rfl

lemma mem_firstOccurrences {ks : List K} {k : K} : k ∈ firstOccurrences ks ↔ k ∈ ks := by
  induction ks using List.reverseRecOn with
  | nil => simp
  | append_singleton ks k' ih =>
    rw [firstOccurrences_append_singleton]
    split_ifs with h
    · rw [mem_append, mem_singleton]
      refine ⟨fun hk => Or.inl (ih.mp hk), ?_⟩
      rintro (hk | rfl)
      · exact ih.mpr hk
      · exact h
    · rw [mem_append, ih, mem_append]

lemma nodup_firstOccurrences (ks : List K) : (firstOccurrences ks).Nodup := by
  induction ks using List.reverseRecOn with
  | nil => exact nodup_nil
  | append_singleton ks k ih =>
    rw [firstOccurrences_append_singleton]
    split_ifs with h
    · exact ih
    · exact ih.append (nodup_singleton k) fun a ha hb => h (mem_singleton.mp hb ▸ ha)

lemma length_firstOccurrences (ks : List K) :
    (firstOccurrences ks).length = ks.toFinset.card := by
  rw [← toFinset_card_of_nodup (nodup_firstOccurrences ks)]
  congr 1
  ext k
  simp only [mem_toFinset, mem_firstOccurrences]

lemma firstOccurrences_prefix (ks ks' : List K) :
    firstOccurrences ks <+: firstOccurrences (ks ++ ks') := by
  induction ks' using List.reverseRecOn with
  | nil => simp
  | append_singleton ks' k ih =>
    rw [← append_assoc, firstOccurrences_append_singleton]
    split_ifs
    · exact ih
    · exact ih.trans (prefix_append _ _)

/-- The rank of a key among the first occurrences does not change as keys are appended. -/
lemma idxOf_firstOccurrences_append {ks : List K} {k : K} (hk : k ∈ ks) (ks' : List K) :
    (firstOccurrences (ks ++ ks')).idxOf k = (firstOccurrences ks).idxOf k := by
  obtain ⟨e, he⟩ := firstOccurrences_prefix ks ks'
  rw [← he, idxOf_append_of_mem (mem_firstOccurrences.mpr hk)]

end List

namespace SystemAlgebra

open Probability

namespace Interface

variable {A : Interface}

/-- The `c`-th entry of a table, below its length. -/
lemma sourceEntry_of_lt {Z : Type} {k : ℕ} (law : Distribution.ProbDist Z) (t : Fin k → Z)
    {c : ℕ} (hc : c < k) : sourceEntry law t c = t ⟨c, hc⟩ := by
  simp only [sourceEntry, sourceStep]
  rw [dif_pos hc]

/-- **The lazy random dictionary** on the table `t`: its state is the list of the keys queried so
far, in the order of their first queries. A query is answered at the entry of `t` at the rank of
its key, which a new key takes as the next one. -/
noncomputable def lazyDictionary (A : Interface) {K Z : Type} [DecidableEq K] {n : ℕ}
    (law : Distribution.ProbDist Z) (t : Fin n → Z) (key : ∀ i, A.X i → K)
    (answer : ∀ i, A.X i → Z → A.Y i) : List K → (i : A.I) → A.X i → List K × A.Y i :=
  fun D i x =>
    let D' := if key i x ∈ D then D else D ++ [key i x]
    (D', answer i x (sourceEntry law t (D'.idxOf (key i x))))

section Lazy

variable {K Z : Type} [DecidableEq K] {n : ℕ} (law : Distribution.ProbDist Z) (t : Fin n → Z)
  (key : ∀ i, A.X i → K) (answer : ∀ i, A.X i → Z → A.Y i)

/-- The dictionary holds the keys queried, in the order of their first queries. -/
lemma stateAfter_lazyDictionary (xs : List (Σ i, A.X i)) :
    stateAfter (lazyDictionary A law t key answer) [] xs =
      List.firstOccurrences (xs.map fun x => key x.1 x.2) := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    rw [stateAfter_snoc, ih, List.map_append, List.map_singleton,
      List.firstOccurrences_append_singleton]
    rfl

/-- **The transcripts of the dictionary on a table**: the admitted transcripts answered at the
entry of the table at the rank of each key among the keys of the transcript. -/
lemma lazyDictionary_replies (tr : List ((Σ i, A.X i) × (Σ i, A.Y i))) :
    Replies (filterDom A.domain (automatonSystem (lazyDictionary A law t key answer) []))
        (tr.map Prod.fst) (tr.map Prod.snd) ↔
      (tr = [] ∨ A.domain (tr.map Prod.fst)) ∧ ∀ z ∈ tr, z.2 = ⟨z.1.1, answer z.1.1 z.1.2
        (sourceEntry law t ((List.firstOccurrences (tr.map fun z => key z.1.1 z.1.2)).idxOf
          (key z.1.1 z.1.2)))⟩ := by
  induction tr using List.reverseRecOn with
  | nil => simp
  | append_singleton tr z ih =>
    simp only [List.map_append, List.map_singleton]
    rw [replies_snoc]
    by_cases hd : A.domain (tr.map Prod.fst ++ [z.1])
    · have hh : tr = [] ∨ A.domain (tr.map Prod.fst) := by
        by_cases hn : tr = []
        · exact Or.inl hn
        · exact Or.inr (A.nonempty_prefix.2 (List.prefix_append _ _) (by simpa using hn) hd)
      rw [ih]
      simp only [hh, hd, or_true, true_and, filterDom, if_true, automatonSystem_snoc,
        stateAfter_lazyDictionary, List.mem_append, List.mem_singleton]
      -- The ranks of the keys of `tr` are their ranks in the whole transcript.
      have rank : ∀ w ∈ tr,
          (List.firstOccurrences ((tr.map fun z => key z.1.1 z.1.2) ++ [key z.1.1 z.1.2])).idxOf
            (key w.1.1 w.1.2) =
          (List.firstOccurrences (tr.map fun z => key z.1.1 z.1.2)).idxOf (key w.1.1 w.1.2) :=
        fun w hw => List.idxOf_firstOccurrences_append (ks := tr.map fun z => key z.1.1 z.1.2)
          (k := key w.1.1 w.1.2) (List.mem_map.mpr ⟨w, hw, rfl⟩) _
      have last : ((lazyDictionary A law t key answer)
          (List.firstOccurrences ((tr.map Prod.fst).map fun x => key x.1 x.2)) z.1.1 z.1.2).2 =
          answer z.1.1 z.1.2 (sourceEntry law t
            ((List.firstOccurrences ((tr.map fun z => key z.1.1 z.1.2) ++
              [key z.1.1 z.1.2])).idxOf (key z.1.1 z.1.2))) := by
        rw [List.map_map, List.firstOccurrences_append_singleton]
        rfl
      rw [last, Part.some_inj]
      constructor
      · rintro ⟨hw, hz⟩ w (hw' | rfl)
        · exact (hw w hw').trans (by rw [rank w hw'])
        · exact hz.symm
      · intro h
        exact ⟨fun w hw' => (h w (Or.inl hw')).trans (by rw [rank w hw']),
          (h z (Or.inr rfl)).symm⟩
    · have hne : ¬ (tr ++ [z] = [] ∨ A.domain (tr.map Prod.fst ++ [z.1])) := by simp [hd]
      simp only [hne, false_and, iff_false, filterDom, if_neg hd]
      exact fun h => Part.some_ne_none _ h.2.symm

end Lazy

/-- **A table of independent samples read at the ranks of distinct keys**: for a list `F` of
distinct keys, no longer than the table, an event depending only on the values at the keys of `F`
has the same mass for the table read at the rank of each key in `F` as for independent samples at
every key. -/
lemma Distribution.mass_pi_sourceEntry_idxOf {K Z : Type} [Fintype K] [DecidableEq K]
    [Fintype Z] [DecidableEq Z] (law : Distribution.ProbDist Z) {n : ℕ} (F : List K)
    (hF : F.Nodup) (hn : F.length ≤ n) (E : (K → Z) → Prop)
    (local_E : ∀ s s', (∀ k ∈ F, s k = s' k) → (E s ↔ E s')) :
    (Distribution.pi fun _ : Fin n => law.1).mass
        (fun t => E fun k => sourceEntry law t (F.idxOf k)) =
      (Distribution.pi fun _ : K => law.1).mass E := by
  classical
  -- Both are the mass of the event at independent samples at the ranks of `F`.
  let extend : (Fin F.length → Z) → K → Z := fun v k => sourceEntry law v (F.idxOf k)
  have rank : ∀ k ∈ F, F.idxOf k < F.length := fun k hk => List.idxOf_lt_length_of_mem hk
  have table : (Distribution.pi fun _ : Fin n => law.1).mass
      (fun t => E fun k => sourceEntry law t (F.idxOf k)) =
      (Distribution.pi fun _ : Fin F.length => law.1).mass (fun v => E (extend v)) := by
    rw [← Distribution.fTransform_pi_comp_injective law.1 law.2.2 (Fin.castLE hn)
      (Fin.castLE_injective hn), Distribution.mass_fTransform]
    refine Distribution.mass_congr _ fun t => local_E _ _ fun k hk => ?_
    simp only [extend]
    rw [sourceEntry_of_lt law _ ((rank k hk).trans_le hn), sourceEntry_of_lt law _ (rank k hk)]
    rfl
  have keys : (Distribution.pi fun _ : K => law.1).mass E =
      (Distribution.pi fun _ : Fin F.length => law.1).mass (fun v => E (extend v)) := by
    rw [← Distribution.fTransform_pi_comp_injective law.1 law.2.2 F.get
      (List.nodup_iff_injective_get.mp hF), Distribution.mass_fTransform]
    refine Distribution.mass_congr _ fun s => local_E _ _ fun k hk => ?_
    simp only [extend]
    rw [sourceEntry_of_lt law _ (rank k hk)]
    exact congrArg s (List.getElem_idxOf (rank k hk)).symm
  rw [table, keys]

/-- **On a transcript, the dictionary on a table is a function**: the function reading the table
at the rank of each key among the keys of the transcript. -/
lemma Resource.ofAutomaton_lazyDictionary_mass {K Z : Type} [DecidableEq K] {n : ℕ}
    (law : Distribution.ProbDist Z) (t : Fin n → Z) (key : ∀ i, A.X i → K)
    (answer : ∀ i, A.X i → Z → A.Y i) (tr : List ((Σ i, A.X i) × (Σ i, A.Y i))) :
    (Resource.ofAutomaton A (lazyDictionary A law t key answer)
        (Distribution.ProbDist.single [])).1 tr =
      (Resource.ofFunction fun i x => answer i x (sourceEntry law t
        ((List.firstOccurrences (tr.map fun z => key z.1.1 z.1.2)).idxOf (key i x)))).1 tr := by
  classical
  rw [Resource.ofAutomaton_mass, Resource.ofFunction_mass]
  change Distribution.mass (Finsupp.single [] 1) _ = _
  rw [Distribution.mass_single]
  exact if_congr (lazyDictionary_replies law t key answer tr) rfl rfl

/-- **Lazy sampling**: the lazy random dictionary on a table of independent samples of `law` is
the function answering each query at independent samples of `law` at every key, sampled once,
when the interface admits no more distinct keys than the table has entries. -/
lemma Resource.sample_lazyDictionary {K Z : Type} [Fintype K] [DecidableEq K] [Fintype Z]
    [DecidableEq Z] (law : Distribution.ProbDist Z) (n : ℕ) (key : ∀ i, A.X i → K)
    (answer : ∀ i, A.X i → Z → A.Y i)
    (distinct : ∀ h, A.domain h → (h.map fun x => key x.1 x.2).toFinset.card ≤ n) :
    Resource.sample (Distribution.pi fun _ : Fin n => law.1)
        (fun t => Resource.ofAutomaton A (lazyDictionary A law t key answer)
          (Distribution.ProbDist.single [])) =
      Resource.sample (Distribution.pi fun _ : K => law.1)
        (fun s => Resource.ofFunction fun i x => answer i x (s (key i x))) := by
  classical
  apply Subtype.ext
  apply RandomSystem.ext
  intro tr
  rw [Resource.sample_mass, Resource.sample_mass]
  simp only [Resource.ofAutomaton_lazyDictionary_mass, Resource.ofFunction_mass]
  -- Both sides are the masses of the event that the transcript is answered at the samples.
  have asMass : ∀ {L : Type} (P : Distribution L) (Q : L → Prop) [DecidablePred Q],
      ∑ l ∈ P.support, P l * (if Q l then 1 else 0) = P.mass Q := by
    intro L P Q _
    unfold Distribution.mass Finsupp.sum
    exact Finset.sum_congr rfl fun l _ => by by_cases hq : Q l <;> simp [hq]
  rw [asMass, asMass]
  let F := List.firstOccurrences (tr.map fun z => key z.1.1 z.1.2)
  let E : (K → Z) → Prop := fun s => (tr = [] ∨ A.domain (tr.map Prod.fst)) ∧
    ∀ z ∈ tr, z.2 = ⟨z.1.1, answer z.1.1 z.1.2 (s (key z.1.1 z.1.2))⟩
  change (Distribution.pi fun _ : Fin n => law.1).mass
      (fun t => E fun k => sourceEntry law t (F.idxOf k)) =
    (Distribution.pi fun _ : K => law.1).mass E
  by_cases hd : tr = [] ∨ A.domain (tr.map Prod.fst)
  · have hn : F.length ≤ n := by
      rw [List.length_firstOccurrences]
      rcases hd with rfl | hd
      · simp
      · have := distinct _ hd
        rwa [List.map_map] at this
    refine Distribution.mass_pi_sourceEntry_idxOf law F (List.nodup_firstOccurrences _) hn E
      fun s s' hs => and_congr Iff.rfl (forall₂_congr fun z hz => ?_)
    rw [hs _ (List.mem_firstOccurrences.mpr (List.mem_map.mpr ⟨z, hz, rfl⟩))]
  · rw [Distribution.mass_eq_zero_of_forall_not _ fun _ h => hd h.1,
      Distribution.mass_eq_zero_of_forall_not _ fun _ h => hd h.1]

/-- **An automaton on a sampled table that answers like the lazy random dictionary** is the
sampled function: if, started on each table `t`, along the domain its states stay related to
those of the dictionary on `t` and it answers as the dictionary does, it is the function
answering each query at independent samples of `law` at every key. -/
lemma Resource.ofAutomaton_eq_sample_of_lazyDictionary {St K Z : Type} [Fintype K]
    [DecidableEq K] [Fintype Z] [DecidableEq Z] (step : St → (i : A.I) → A.X i → St × A.Y i)
    (law : Distribution.ProbDist Z) {n : ℕ} (init : (Fin n → Z) → St) (key : ∀ i, A.X i → K)
    (answer : ∀ i, A.X i → Z → A.Y i) (rel : (Fin n → Z) → St → List K → Prop)
    (start : ∀ t, rel t (init t) [])
    (answers : ∀ t h x st D, A.domain (h ++ [x]) → rel t st D →
      (step st x.1 x.2).2 = (lazyDictionary A law t key answer D x.1 x.2).2 ∧
        rel t (step st x.1 x.2).1 (lazyDictionary A law t key answer D x.1 x.2).1)
    (distinct : ∀ h, A.domain h → (h.map fun x => key x.1 x.2).toFinset.card ≤ n) :
    Resource.ofAutomaton A step ⟨Distribution.fTransform init
        (Distribution.pi fun _ : Fin n => law.1),
        Distribution.fTransform_isProbDist _ (Distribution.pi_isProbDist fun _ => law.2)⟩ =
      Resource.sample (Distribution.pi fun _ : K => law.1)
        (fun s => Resource.ofFunction fun i x => answer i x (s (key i x))) := by
  rw [Resource.ofAutomaton_fTransform, ← Resource.sample_lazyDictionary law n key answer distinct]
  congr 1
  funext t
  exact Resource.ofAutomaton_single_congr_on_domain (fun _ st D => rel t st D) (start t)
    fun h x st D hd hr => answers t h x st D hd hr

/-- **An association list holding the dictionary**: if `T` holds the value `f r` at the code of
each key of `D` of rank `r`, and nothing at the codes of other keys, then appending a new key `k`
with the value of the next rank holds the dictionary `D ++ [k]`. -/
lemma lookup_append_of_dictionary {K K' V : Type} [DecidableEq K] [BEq K'] [LawfulBEq K']
    (code : K → K') (hcode : Function.Injective code) {T : List (K' × V)} {D : List K}
    {f : ℕ → V} (hT : ∀ k, T.lookup (code k) = if k ∈ D then some (f (D.idxOf k)) else none)
    {k : K} (hk : k ∉ D) (k' : K) :
    (T ++ [(code k, f D.length)]).lookup (code k') =
      if k' ∈ D ++ [k] then some (f ((D ++ [k]).idxOf k')) else none := by
  rw [List.lookup_append, hT]
  by_cases h : k' = k
  · subst h
    simp [hk, List.idxOf_append_of_notMem hk]
  · by_cases h' : k' ∈ D
    · simp [h', List.idxOf_append_of_mem h']
    · have hne : (code k' == code k) = false := beq_false_of_ne (hcode.ne h)
      simp [h', h, List.lookup_cons, hne]

/-- **A program attached to an automaton started on a sampled table** is the combined automaton
started on the table. A system compiled from sampling statements is a program on its source, an
automaton started on its table, and so is a program attached to it. -/
lemma ofDDC_ofProgramOn_smul_ofAutomaton_pi {B : Interface} {S R Z : Type} {n : ℕ} (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    (hα : IsDDCFrom B.domain A.domain b (DDC.ofProgramOn s P A.domain))
    (stepR : R → (j : B.I) → B.X j → R × B.Y j) (law : Distribution.ProbDist Z)
    (init : (Fin n → Z) → R) :
    Interface.ofDDC (DDC.ofProgramOn s P A.domain) hα • Resource.ofAutomaton B stepR
        ⟨Distribution.fTransform init (Distribution.pi fun _ : Fin n => law.1),
          Distribution.fTransform_isProbDist _ (Distribution.pi_isProbDist fun _ => law.2)⟩ =
      Resource.ofAutomaton A (P.combine stepR hb)
        ⟨Distribution.fTransform (fun t => (s, init t)) (Distribution.pi fun _ : Fin n => law.1),
          Distribution.fTransform_isProbDist _ (Distribution.pi_isProbDist fun _ => law.2)⟩ := by
  rw [Interface.ofDDC_ofProgramOn_smul_ofAutomaton s P hb]
  congr 1
  exact Subtype.ext (Distribution.fTransform_comp _ _ _)

end Interface

end SystemAlgebra
