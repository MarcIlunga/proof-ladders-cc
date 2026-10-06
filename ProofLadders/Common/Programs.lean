import ConstructiveCryptography.DSL.Converters
import ConstructiveCryptography.DSL.Programs

/-!
# Programs at per-label budgets, and serial composition of programs

A program can make several inside queries per invocation at several inside labels. A per-label
call bound counts its queries at each inside label: at most `c o j` queries at the label `j` per
invocation at the outside label `o`. Along its transcripts the program then queries `j` at most
`∑ o, c o j · n_o` times on `n_o` outside queries at each `o`, and it is a converter from outside
histories with at most `q o` queries at each `o` to every inside interface admitting the
histories with at most `∑ o, c o j · q o` queries at each `j`: a per-port interface, a source, or
a parallel interface of such.

An amortized per-label call bound adds a potential `φ` on the program's states: an invocation at
`o` from the state `s` makes at most `c o j + φ s j` queries at `j`, and leaves a state `s'` with
`φ s' j` at most what remains of them. The potentials telescope along transcripts, so the program
queries `j` at most `∑ o, c o j · n_o + φ s₀ j` times from its initial state `s₀`: a query made
once in a run, such as fetching a challenge, costs one from the potential instead of one per
invocation. The per-label call bound is the case `φ = 0`.

The DSL types a program by a total bound (`Interface.Converter.ofProgram`), by exact costs
(`Interface.Converter.ofCostedProgram`), or along a port map that gives each procedure one inside
label (`Interface.Converter.ofPreservingProgram`); the per-label bound types the programs whose
procedures call several inside labels.

Two programs in series are one program: the composed body runs the outer body and answers each
of its queries by running the inner body on it, whose inside queries are those of the composed
program. The serial composition of the two converters replies as the composed program, so it is
the converter of the composed program; programs that are bisimilar on the exchanges they make
are one converter.

Upstream candidates: `Program.LabelCallBound`, `Program.LabelBounded`,
`Program.labelCallBound_return`, `Program.labelCallBound_call`, `Program.LabelCallBoundWith`,
`Program.LabelBoundedWith`, `Program.LabelBounded.labelBoundedWith`,
`Program.labelCallBoundWith_return`, `Program.labelCallBoundWith_call`, `Program.Mode.labelCredit`,
`DDC.insideQueries_restrict_length_le_of_labelBoundedWith` and
`DDC.insideQueries_restrict_length_le_of_labelBounded` for `RandomSystems.Converter.Program`, beside
`DDC.insideQueries_restrict_length_le`; `sum_map_eq_sum_mul_length_restrict` and
`restrict_restrict_some_sumAlphabet` for `RandomSystems.System.Basic` and
`RandomSystems.Converter.ConverterTensor`; `Interface.AdmitsLabelBudget`, its instances and
`Interface.Converter.ofLabelBoundedProgram` and `Interface.Converter.ofAmortizedProgram` for
`ConstructiveCryptography.DSL.Converters`, beside `Interface.Converter.ofPreservingProgram`;
`Program.serialLoop`, `Program.serial`, `Program.Consistent.length_le`, `Exchange.dom_of_some`,
`Program.SerialOutcome`, `Program.serial_exchange`, `Program.SerialInv`, `Program.replies_serial`
and `DDC.ofProgram_eq_of_bisim` for `RandomSystems.DDC.Serial`, beside `serialM`; and
`Interface.ofDDC_ofProgramOn_comp` for `ConstructiveCryptography.DSL.Converters`, beside
`PDCBehavior.comp_ofDDC`.

## Main definitions

* `Program.LabelCallBound n f`, `Program.LabelBounded c P`: at most `n j` inside queries at `j`
  per body, and at most `c o j` per invocation at `o`
* `Program.LabelCallBoundWith n ψ f`, `Program.LabelBoundedWith c φ P`: amortized per-label call
  bounds, with the potential `ψ` of a result and `φ` of a state
* `Interface.AdmitsLabelBudget B k`: `B` admits the nonempty histories with at most `k j` queries
  at each label `j`
* `Interface.Converter.ofLabelBoundedProgram s P hb c hc q hA hB`: the converter of a program at
  per-label budgets
* `Interface.Converter.ofAmortizedProgram s P hb c φ hc q hA hB`: the converter of a program at
  amortized per-label budgets
* `Program.serial P₁ P₂ b₁ v₀`: the composed program of `P₁` followed by `P₂`, from the serial
  loop `Program.serialLoop`

## Main results

* `DDC.insideQueries_restrict_length_le_of_labelBoundedWith`,
  `DDC.insideQueries_restrict_length_le_of_labelBounded`: the per-label count along transcripts
* `Interface.portBudget_admitsLabelBudget`, `Interface.queryBudget_admitsLabelBudget`,
  `Interface.AdmitsLabelBudget.tensor`, `Interface.portBudget_tensor_admitsLabelBudget`: the
  inside interfaces at per-label budgets
* `Program.serial_exchange`, `Program.replies_serial`: the serial loop is an exchange of the
  serial composition, which replies as the composed program
* `DDC.ofProgram_eq_of_bisim`: bisimilar programs are one converter
* `Interface.ofDDC_ofProgramOn_comp`: the serial composition of two program converters is the
  converter of the composed program
-/

namespace SystemAlgebra

open Classical

variable {S O J : Type} {U V : O → Type} {X Y : J → Type}

/-- **Outside costs by label**: the total of a cost per label over a history is the sum over the
labels of the cost times the number of queries there. -/
lemma sum_map_eq_sum_mul_length_restrict {K : Type} [Fintype K] {A : K → Type} (c : K → ℕ)
    (xs : List (Σ k, A k)) :
    (xs.map fun x => c x.1).sum = ∑ k, c k * (restrict k xs).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons, ih, show x :: xs = [x] ++ xs from rfl]
    simp only [restrict_append, List.length_append, length_restrict_singleton, Nat.mul_add,
      Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]

/-- The queries at a right label of a parallel history are those of its right projection. -/
lemma restrict_restrict_some_sumAlphabet {I J : Type} {F : I ⊕ J → Type} (j : J)
    (ys : List (Σ l, F l)) :
    restrict j (restrict (some ()) (ys.map (sumAlphabet F).symm)) = restrict (Sum.inr j) ys := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    rcases y with ⟨(i | j'), x⟩
    · change restrict j (restrict (some ()) ((⟨none, ⟨i, x⟩⟩ : Two _ _) ::
        ys.map (sumAlphabet F).symm)) = restrict (Sum.inr j) (⟨Sum.inl i, x⟩ :: ys)
      rw [restrict_cons_ne (by simp), restrict_cons_ne (by simp), ih]
    · change restrict j (restrict (some ()) ((⟨some (), ⟨j', x⟩⟩ : Two _ _) ::
        ys.map (sumAlphabet F).symm)) = restrict (Sum.inr j) (⟨Sum.inr j', x⟩ :: ys)
      rw [restrict_cons_self]
      by_cases hj : j' = j
      · subst hj
        rw [restrict_cons_self, restrict_cons_self, ih]
      · rw [restrict_cons_ne hj, restrict_cons_ne (by simpa using hj), ih]

namespace Program

open Program (ExchangesOf)

/-- **A per-label call bound** of a body: along its own exchanges, it queries each label `j` at
most `n j` times. -/
def LabelCallBound {A : Type} (n : J → ℕ) (f : List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)) :
    Prop :=
  ∀ h q, ExchangesOf f h → f h = .inr q → (restrict q.1 (h.map Prod.fst)).length < n q.1

/-- At most `c o j` inside queries at the label `j` per invocation at the outside label `o`. -/
def LabelBounded (c : O → J → ℕ) (P : Program S O J U V X Y) : Prop :=
  ∀ s o u, LabelCallBound (c o) (P s o u)

lemma labelCallBound_return {A : Type} (n : J → ℕ) (a : A) :
    LabelCallBound (X := X) (Y := Y) n (DSL.returnProg a) := by
  intro h q _ hq
  cases hq

/-- A call at `j` spends one query of the budget at `j`, and its continuation the rest. -/
lemma labelCallBound_call {A : Type} [DecidableEq J] {n : J → ℕ} (j : J) (x : X j)
    (k : Y j → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)) (hj : 0 < n j)
    (hk : ∀ y, LabelCallBound (fun i => if i = j then n i - 1 else n i) (k y)) :
    LabelCallBound n (DSL.callProg j x k) := by
  intro h q hc hq
  rcases h with _ | ⟨z, h⟩
  · cases hq
    simpa using hj
  · obtain ⟨y, rfl, he, hc'⟩ := DSL.exchangesOf_callProg hc
    rw [he] at hq
    have hb := hk y h q hc' hq
    rw [List.map_cons, show (⟨j, x⟩ : Σ j, X j) :: h.map Prod.fst = [⟨j, x⟩] ++ h.map Prod.fst
      from rfl, restrict_append, List.length_append, length_restrict_singleton]
    dsimp only at hb
    by_cases hqj : q.1 = j
    · rw [if_pos hqj.symm]
      rw [if_pos hqj] at hb
      rw [hqj] at hb ⊢
      omega
    · rw [if_neg (Ne.symm hqj)]
      rw [if_neg hqj] at hb
      omega

/-- **An amortized per-label call bound** of a body with results in `A`: it is at the per-label
call bound `n`, and a result `a` it reaches leaves `ψ a j` within what remains of `n j`. -/
def LabelCallBoundWith {A : Type} (n : J → ℕ) (ψ : A → J → ℕ)
    (f : List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)) : Prop :=
  LabelCallBound n f ∧
    ∀ h a, ExchangesOf f h → f h = .inl a → ∀ j, ψ a j ≤ n j - (restrict j (h.map Prod.fst)).length

/-- **An amortized per-label call bound** with the potential `φ` on states: an invocation at `o`
from the state `s` makes at most `c o j + φ s j` inside queries at `j`, and the state `s'` it
ends in has `φ s' j` at most what remains of them. -/
def LabelBoundedWith (c : O → J → ℕ) (φ : S → J → ℕ) (P : Program S O J U V X Y) : Prop :=
  ∀ s o u, LabelCallBoundWith (fun j => c o j + φ s j) (fun r => φ r.1) (P s o u)

/-- A per-label call bound is the amortized one with the potential `0`. -/
lemma LabelBounded.labelBoundedWith {c : O → J → ℕ} {P : Program S O J U V X Y}
    (hP : P.LabelBounded c) : P.LabelBoundedWith c 0 :=
  fun s o u => ⟨hP s o u, fun _ _ _ _ _ => Nat.zero_le _⟩

/-- A return leaves its result's potential within the bound. -/
lemma labelCallBoundWith_return {A : Type} {n : J → ℕ} {ψ : A → J → ℕ} (a : A)
    (ha : ∀ j, ψ a j ≤ n j) : LabelCallBoundWith (X := X) (Y := Y) n ψ (DSL.returnProg a) := by
  refine ⟨labelCallBound_return n a, fun h a' hc he j => ?_⟩
  rcases h with _ | ⟨z, h⟩
  · cases he
    simpa using ha j
  · exact absurd (hc 0 (by simp)).1 (by simp [DSL.returnProg])

/-- A call at `j` spends one query of the budget at `j`, and its continuation the rest. -/
lemma labelCallBoundWith_call {A : Type} [DecidableEq J] {n : J → ℕ} {ψ : A → J → ℕ} (j : J)
    (x : X j) (k : Y j → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)) (hj : 0 < n j)
    (hk : ∀ y, LabelCallBoundWith (fun i => if i = j then n i - 1 else n i) ψ (k y)) :
    LabelCallBoundWith n ψ (DSL.callProg j x k) := by
  refine ⟨labelCallBound_call j x k hj fun y => (hk y).1, fun h a hc he i => ?_⟩
  rcases h with _ | ⟨z, h⟩
  · simp [DSL.callProg] at he
  · obtain ⟨y, rfl, he', hc'⟩ := DSL.exchangesOf_callProg hc
    rw [he'] at he
    have hb := (hk y).2 h a hc' he i
    rw [List.map_cons, show (⟨j, x⟩ : Σ j, X j) :: h.map Prod.fst = [⟨j, x⟩] ++ h.map Prod.fst
      from rfl, restrict_append, List.length_append, length_restrict_singleton]
    dsimp only at hb
    by_cases hij : i = j
    · subst hij
      simp only [if_true] at hb ⊢
      omega
    · simp only [hij, Ne.symm hij, if_false] at hb ⊢
      omega

/-- The queries at `j` the program may still make within its amortized per-label bound: the
potential of the state when idle, and what remains of the current invocation's bound when busy. -/
noncomputable def Mode.labelCredit (c : O → J → ℕ) (φ : S → J → ℕ) (j : J) :
    Mode S O J U X Y → ℕ
  | .idle s => φ s j
  | .busy o s _ h q =>
    c o j + φ s j - ((restrict j (h.map Prod.fst)).length + if q.1 = j then 1 else 0)

end Program

namespace DDC

variable {s : S} {P : Program S O J U V X Y}

/-- **A program at an amortized per-label call bound** makes, along its transcripts, at most
`c o j` inside queries at `j` for each outside query at `o`, and `φ s j` more from its initial
state `s`. -/
lemma insideQueries_restrict_length_le_of_labelBoundedWith {c : O → J → ℕ} {φ : S → J → ℕ}
    (hP : P.LabelBoundedWith c φ) {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (DDC.ofProgram s P) (h.map Prod.fst) (h.map Prod.snd)) (j : J) :
    (restrict j (insideQueries (h.map Prod.snd))).length ≤
      ((outsideInputs (h.map Prod.fst)).map fun x => c x.1 j).sum + φ s j := by
  suffices key : ∀ m, P.after s (h.map Prod.fst) = some m →
      (restrict j (insideQueries (h.map Prod.snd))).length + m.labelCredit c φ j ≤
        ((outsideInputs (h.map Prod.fst)).map fun x => c x.1 j).sum + φ s j by
    obtain ⟨m, hm⟩ := after_of_replies hr
    exact (Nat.le_add_right _ _).trans (key m hm)
  induction h using List.reverseRecOn with
  | nil =>
    intro m hm
    obtain rfl : m = .idle s := (Option.some.inj hm).symm
    simp [insideQueries, outsideInputs, Program.Mode.labelCredit]
  | append_singleton h z ih =>
    intro m hm
    rcases z with ⟨x, y⟩
    simp only [List.map_append, List.map_singleton] at hr hm ⊢
    obtain ⟨hr₀, hy⟩ := replies_snoc.mp hr
    obtain ⟨m₀, hm₀⟩ := after_of_replies hr₀
    have prior := ih hr₀ m₀ hm₀
    have hmem : y ∈ DDC.ofProgram s P (h.map Prod.fst ++ [x]) := by rw [hy]; exact Part.mem_some y
    obtain ⟨m₁, m', h₁, hs⟩ := (mem_ofProgram_snoc s P _ x y).mp hmem
    rw [hm₀] at h₁
    obtain rfl := Option.some.inj h₁
    have hm' : P.after s (h.map Prod.fst ++ [x]) = some m' :=
      (Program.after_snoc_eq_some P s _ x m').mpr ⟨m₀, y, hm₀, hs⟩
    rw [hm] at hm'
    obtain rfl := Option.some.inj hm'
    have sound₀ := (after_invariant hm₀).1
    rw [insideQueries_append, outsideInputs_append, restrict_append, List.length_append,
      List.map_append, List.sum_append]
    rcases Program.step_cases P hs with ⟨s', o, u, rfl, rfl, he⟩ |
        ⟨o, s', u, hs', q, v, rfl, rfl, he⟩
    · rcases Program.emit_cases P s' o u [] with ⟨s'', w, hw, hE⟩ | ⟨q, hq, hE⟩
      · -- An invocation answered at once: its end state's potential is within its bound.
        rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        have hb := (hP s' o u).2 [] (s'', w) (Program.consistent_nil P s' o u) hw j
        simp only [Program.Mode.labelCredit] at prior ⊢
        simp only [List.map_nil, restrict_nil, List.length_nil, Nat.sub_zero] at hb
        simp only [insideQueries_outside, outsideInputs_outside, restrict_nil, List.length_nil,
          add_zero, List.map_singleton, List.sum_singleton]
        omega
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        have hb := (hP s' o u).1 [] q (Program.consistent_nil P s' o u) hq
        simp only [Program.Mode.labelCredit] at prior
        simp only [insideQueries_inside, outsideInputs_outside, length_restrict_singleton,
          Program.Mode.labelCredit, List.map_nil, restrict_nil, List.length_nil, zero_add,
          List.map_singleton, List.sum_singleton] at hb ⊢
        split_ifs with hqj <;> first | omega | (subst hqj; omega)
    · rcases Program.emit_cases P s' o u (hs' ++ [(q, ⟨q.1, v⟩)]) with
          ⟨s'', w, hw, hE⟩ | ⟨q', hq', hE⟩
      · -- The end of an invocation: its end state's potential is within what remains.
        rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        have hb := (hP s' o u).2 _ (s'', w) (sound₀.1.snoc sound₀.2 v) hw j
        simp only [List.map_append, List.map_singleton, restrict_append, List.length_append,
          length_restrict_singleton] at hb
        simp only [Program.Mode.labelCredit] at prior ⊢
        simp only [insideQueries_outside, restrict_nil, List.length_nil, add_zero]
        rw [show outsideInputs [(⟨⟨some (), q.1⟩, v⟩ : Σ l, twoFam U Y l)] = [] from
          outsideInputs_inside _ _]
        simp only [List.map_nil, List.sum_nil, add_zero]
        omega
      · rw [hE] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        have hb := (hP s' o u).1 _ q' (sound₀.1.snoc sound₀.2 v) hq'
        rw [show outsideInputs [(⟨⟨some (), q.1⟩, v⟩ : Σ l, twoFam U Y l)] = [] from
          outsideInputs_inside _ _]
        simp only [Program.Mode.labelCredit] at prior
        simp only [List.map_append, List.map_singleton, restrict_append, List.length_append,
          length_restrict_singleton] at hb
        simp only [insideQueries_inside, length_restrict_singleton, Program.Mode.labelCredit,
          List.map_append, List.map_singleton, restrict_append, List.length_append,
          List.map_nil, List.sum_nil, add_zero]
        by_cases hq'j : q'.1 = j
        · subst hq'j
          simp only [if_true] at hb ⊢
          split_ifs at prior hb ⊢ <;> omega
        · simp only [hq'j, if_false, add_zero]
          split_ifs at prior ⊢ <;> omega

/-- **A program at a per-label call bound** makes, along its transcripts, at most `c o j` inside
queries at `j` for each outside query at `o`. -/
lemma insideQueries_restrict_length_le_of_labelBounded {c : O → J → ℕ}
    (hP : P.LabelBounded c) {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (DDC.ofProgram s P) (h.map Prod.fst) (h.map Prod.snd)) (j : J) :
    (restrict j (insideQueries (h.map Prod.snd))).length ≤
      ((outsideInputs (h.map Prod.fst)).map fun x => c x.1 j).sum :=
  insideQueries_restrict_length_le_of_labelBoundedWith hP.labelBoundedWith hr j

end DDC

namespace Interface

/-- **`B` admits the per-label budget `k`**: every nonempty history with at most `k j` queries at
each label `j`. -/
def AdmitsLabelBudget (B : Interface) (k : B.I → ℕ) : Prop :=
  ∀ ys, ys ≠ [] → (∀ j, (SystemAlgebra.restrict j ys).length ≤ k j) → B.domain ys

lemma AdmitsLabelBudget.mono {B : Interface} {k k' : B.I → ℕ} (hB : B.AdmitsLabelBudget k)
    (hk : ∀ j, k' j ≤ k j) : B.AdmitsLabelBudget k' :=
  fun ys hne hys => hB ys hne fun j => (hys j).trans (hk j)

/-- A per-port interface admits its budget. -/
lemma portBudget_admitsLabelBudget (I : Type) [Fintype I] (X Y : I → Type)
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] (k : I → ℕ) :
    (portBudget I X Y k).AdmitsLabelBudget k :=
  fun _ hne hk => ⟨hne, hk⟩

/-- An interface of at most `n` queries, a source for instance, admits every per-label budget
of total at most `n`. -/
lemma queryBudget_admitsLabelBudget (I : Type) [Fintype I] (X Y : I → Type)
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] {n : ℕ} (k : I → ℕ) (hk : ∑ i, k i ≤ n) :
    (queryBudget I X Y n).AdmitsLabelBudget k :=
  fun ys hne hys => ⟨hne, (length_eq_sum_restrict ys).trans_le
    ((Finset.sum_le_sum fun i _ => hys i).trans hk)⟩

/-- **A parallel interface** admits the per-label budgets of its two sides. -/
lemma AdmitsLabelBudget.tensor {A B : Interface} {k₁ : A.I → ℕ} {k₂ : B.I → ℕ}
    (hA : A.AdmitsLabelBudget k₁) (hB : B.AdmitsLabelBudget k₂) :
    (A.tensor B).AdmitsLabelBudget (Sum.elim k₁ k₂) := by
  intro ys hne hys
  refine ⟨hne, ?_, ?_⟩
  · by_cases he : SystemAlgebra.restrict none (ys.map (sumAlphabet (Sum.rec A.X B.X)).symm) = []
    · exact Or.inl he
    · exact Or.inr (hA _ he fun i => by rw [restrict_restrict_sumAlphabet]; exact hys (.inl i))
  · by_cases he :
        SystemAlgebra.restrict (some ()) (ys.map (sumAlphabet (Sum.rec A.X B.X)).symm) = []
    · exact Or.inl he
    · exact Or.inr (hB _ he fun j => by
        rw [restrict_restrict_some_sumAlphabet]; exact hys (.inr j))

/-- **Two per-port interfaces in parallel** admit their two budgets. -/
lemma portBudget_tensor_admitsLabelBudget (I I' : Type) [Fintype I] [Fintype I']
    (X Y : I → Type) [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] (X' Y' : I' → Type)
    [∀ i, Fintype (X' i)] [∀ i, Fintype (Y' i)] (k : I → ℕ) (k' : I' → ℕ) :
    ((portBudget I X Y k).tensor (portBudget I' X' Y' k')).AdmitsLabelBudget (Sum.elim k k') :=
  (portBudget_admitsLabelBudget I X Y k).tensor (portBudget_admitsLabelBudget I' X' Y' k')

/-- **The converter of a program at per-label budgets**: on outside histories with at most `q o`
queries at each label `o`, a program making at most `c o j` inside queries at `j` per invocation
at `o` makes at most `∑ o, c o j · q o` inside queries at `j`, which `B` admits. -/
noncomputable def Converter.ofLabelBoundedProgram {A B : Interface} (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b) (c : A.I → B.I → ℕ)
    (hc : P.LabelBounded c) (q : A.I → ℕ)
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : B.AdmitsLabelBudget fun j => ∑ o, c o j * q o) : A ⟶ B :=
  Interface.ofDDC (DDC.ofProgramOn s P A.domain)
    (DDC.ofProgramOn_isDDCFrom hb A.nonempty_prefix.2 fun h hr hF => by
      by_cases hne : insideQueries (h.map Prod.snd) = []
      · exact Or.inl hne
      · refine Or.inr (hB _ hne fun j =>
          (DDC.insideQueries_restrict_length_le_of_labelBounded hc hr j).trans ?_)
        rw [sum_map_eq_sum_mul_length_restrict (fun o => c o j)]
        rcases hF with he | hF
        · rw [he]
          simp
        · exact Finset.sum_le_sum fun o _ => Nat.mul_le_mul_left _ (hA _ hF o))

/-- **The converter of a program at amortized per-label budgets**: on outside histories with at
most `q o` queries at each label `o`, a program at the per-label call bound `c` with the
potential `φ` makes at most `∑ o, c o j · q o + φ s j` inside queries at `j` from its initial
state `s`, which `B` admits. -/
noncomputable def Converter.ofAmortizedProgram {A B : Interface} (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b) (c : A.I → B.I → ℕ)
    (φ : S → B.I → ℕ) (hc : P.LabelBoundedWith c φ) (q : A.I → ℕ)
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : B.AdmitsLabelBudget fun j => ∑ o, c o j * q o + φ s j) : A ⟶ B :=
  Interface.ofDDC (DDC.ofProgramOn s P A.domain)
    (DDC.ofProgramOn_isDDCFrom hb A.nonempty_prefix.2 fun h hr hF => by
      by_cases hne : insideQueries (h.map Prod.snd) = []
      · exact Or.inl hne
      · refine Or.inr (hB _ hne fun j =>
          (DDC.insideQueries_restrict_length_le_of_labelBoundedWith hc hr j).trans
            (Nat.add_le_add_right ?_ _))
        rw [sum_map_eq_sum_mul_length_restrict (fun o => c o j)]
        rcases hF with he | hF
        · rw [he]
          simp
        · exact Finset.sum_le_sum fun o _ => Nat.mul_le_mul_left _ (hA _ hF o))

end Interface

/-! ## Serial composition of programs -/

section Serial

open CategoryTheory

namespace Program

variable {S₁ S₂ O M J : Type} {U V : O → Type} {Xm Ym : M → Type} {X Y : J → Type}

/-- **The serial loop** of two bodies, in the outer invocation `(s₁, o, u)`: the outer body has
the exchanges `h₁` with the middle interface, the inner body the state `s₂` and the exchanges `h₂`
of its invocation, and the inside exchanges `h` are still to be fed. A round runs the outer body;
on a middle query it runs the inner body on it, which replies to the outer body or queries the
inside, answered by the next exchange of `h`. At most `n` rounds; `v₀` is a reply for none. -/
noncomputable def serialLoop (P₁ : Program S₁ O M U V Xm Ym) (P₂ : Program S₂ M J Xm Ym X Y)
    (s₁ : S₁) (o : O) (u : U o) (v₀ : V o) :
    ℕ → List ((Σ m, Xm m) × (Σ m, Ym m)) → S₂ → List ((Σ j, X j) × (Σ j, Y j)) →
      List ((Σ j, X j) × (Σ j, Y j)) → ((S₁ × S₂) × V o) ⊕ (Σ j, X j)
  | 0, _, s₂, _, _ => .inl ((s₁, s₂), v₀)
  | n + 1, h₁, s₂, h₂, h =>
    match P₁ s₁ o u h₁ with
    | .inl (s₁', v) => .inl ((s₁', s₂), v)
    | .inr q₁ =>
      match P₂ s₂ q₁.1 q₁.2 h₂ with
      | .inl (s₂', y) => serialLoop P₁ P₂ s₁ o u v₀ n (h₁ ++ [(q₁, ⟨q₁.1, y⟩)]) s₂' [] h
      | .inr q₂ =>
        match h with
        | [] => .inr q₂
        | e :: h' => serialLoop P₁ P₂ s₁ o u v₀ n h₁ s₂ (h₂ ++ [e]) h'

/-- **The serial composition of two programs**: the program on pairs of states whose body is the
serial loop from the invocation's start, with `b₁ + 1` rounds beyond its inside exchanges, enough
for an outer body making at most `b₁` middle queries. -/
noncomputable def serial (P₁ : Program S₁ O M U V Xm Ym) (P₂ : Program S₂ M J Xm Ym X Y)
    (b₁ : ℕ) (v₀ : ∀ o, V o) : Program (S₁ × S₂) O J U V X Y :=
  fun s o u h => serialLoop P₁ P₂ s.1 o u (v₀ o) (b₁ + 1 + h.length) [] s.2 [] h

variable {P₁ : Program S₁ O M U V Xm Ym} {P₂ : Program S₂ M J Xm Ym X Y} {s₁ : S₁} {o : O}
  {u : U o} {v₀ : V o}

lemma serialLoop_return {n : ℕ} {h₁ : List ((Σ m, Xm m) × (Σ m, Ym m))} {s₂ : S₂}
    {h₂ h : List ((Σ j, X j) × (Σ j, Y j))} {s₁' : S₁} {v : V o}
    (h1 : P₁ s₁ o u h₁ = .inl (s₁', v)) :
    serialLoop P₁ P₂ s₁ o u v₀ (n + 1) h₁ s₂ h₂ h = .inl ((s₁', s₂), v) := by
  simp [serialLoop, h1]

lemma serialLoop_inner_return {n : ℕ} {h₁ : List ((Σ m, Xm m) × (Σ m, Ym m))} {s₂ : S₂}
    {h₂ h : List ((Σ j, X j) × (Σ j, Y j))} {q₁ : Σ m, Xm m} {s₂' : S₂} {y : Ym q₁.1}
    (h1 : P₁ s₁ o u h₁ = .inr q₁) (h2 : P₂ s₂ q₁.1 q₁.2 h₂ = .inl (s₂', y)) :
    serialLoop P₁ P₂ s₁ o u v₀ (n + 1) h₁ s₂ h₂ h =
      serialLoop P₁ P₂ s₁ o u v₀ n (h₁ ++ [(q₁, ⟨q₁.1, y⟩)]) s₂' [] h := by
  simp [serialLoop, h1, h2]

lemma serialLoop_query {n : ℕ} {h₁ : List ((Σ m, Xm m) × (Σ m, Ym m))} {s₂ : S₂}
    {h₂ : List ((Σ j, X j) × (Σ j, Y j))} {q₁ : Σ m, Xm m} {q₂ : Σ j, X j}
    (h1 : P₁ s₁ o u h₁ = .inr q₁) (h2 : P₂ s₂ q₁.1 q₁.2 h₂ = .inr q₂) :
    serialLoop P₁ P₂ s₁ o u v₀ (n + 1) h₁ s₂ h₂ [] = .inr q₂ := by
  simp [serialLoop, h1, h2]

lemma serialLoop_feed {n : ℕ} {h₁ : List ((Σ m, Xm m) × (Σ m, Ym m))} {s₂ : S₂}
    {h₂ h : List ((Σ j, X j) × (Σ j, Y j))} {e : (Σ j, X j) × (Σ j, Y j)} {q₁ : Σ m, Xm m}
    {q₂ : Σ j, X j} (h1 : P₁ s₁ o u h₁ = .inr q₁) (h2 : P₂ s₂ q₁.1 q₁.2 h₂ = .inr q₂) :
    serialLoop P₁ P₂ s₁ o u v₀ (n + 1) h₁ s₂ h₂ (e :: h) =
      serialLoop P₁ P₂ s₁ o u v₀ n h₁ s₂ (h₂ ++ [e]) h := by
  simp [serialLoop, h1, h2]

/-- A consistent history of a bounded body is within its bound. -/
lemma Consistent.length_le {S O J : Type} {U V : O → Type} {X Y : J → Type}
    {P : Program S O J U V X Y} {b : ℕ} (hP : P.Bounded b) {s : S} {o : O} {u : U o}
    {h : List ((Σ j, X j) × (Σ j, Y j))} (hc : P.Consistent s o u h) : h.length ≤ b := by
  rcases List.eq_nil_or_concat h with rfl | ⟨h', z, rfl⟩
  · exact Nat.zero_le _
  · rw [List.concat_eq_append] at hc ⊢
    have hz := hc h'.length (by simp)
    rw [List.take_left' rfl, List.getElem_append_right (le_refl _)] at hz
    have hc' : P.Consistent s o u h' := fun i hi => by
      have := hc i (by simp; omega)
      rwa [List.take_append_of_le_length hi.le, List.getElem_append_left hi] at this
    have := hP s o u h' _ hc' (by simpa using hz.1)
    simp only [List.length_append, List.length_singleton]
    omega

section Exchange

variable (s₁ : S₁) (s₂ : S₂) (P₁ : Program S₁ O M U V Xm Ym) (P₂ : Program S₂ M J Xm Ym X Y)
  (v₀ : ∀ o, V o)

/-- The outcome of the serial loop from a configuration, as an exchange of the serial
composition of the two programs' converters. -/
def SerialOutcome (n : ℕ) (G : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Y l))) (t₁ : S₁)
    (o : O) (u : U o) (h₁ : List ((Σ m, Xm m) × (Σ m, Ym m))) (t₂ : S₂)
    (h₂ : List ((Σ j, X j) × (Σ j, Y j))) : Prop :=
  (∀ t₁' t₂' v, serialLoop P₁ P₂ t₁ o u (v₀ o) n h₁ t₂ h₂ [] = .inl ((t₁', t₂'), v) →
    ∃ G', Exchange (pair (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂)) serialRouteM G
        (some (⟨⟨none, o⟩, v⟩ : Σ l, twoFam V X l)) G' ∧
      P₁.after s₁ (restrict none G') = some (.idle t₁') ∧
      P₂.after s₂ (restrict (some ()) G') = some (.idle t₂')) ∧
  (∀ q : Σ j, X j, serialLoop P₁ P₂ t₁ o u (v₀ o) n h₁ t₂ h₂ [] = .inr q →
    ∃ G' h₁' q₁' t₂' h₂' k, Exchange (pair (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂))
        serialRouteM G (some (⟨⟨some (), q.1⟩, q.2⟩ : Σ l, twoFam V X l)) G' ∧
      P₁.after s₁ (restrict none G') = some (.busy o t₁ u h₁' q₁') ∧
      P₂.after s₂ (restrict (some ()) G') = some (.busy q₁'.1 t₂' q₁'.2 h₂' q) ∧
      h₁'.length = h₁.length + k ∧
      ∀ m hrest, serialLoop P₁ P₂ t₁ o u (v₀ o) (m + k) h₁ t₂ h₂ hrest =
        serialLoop P₁ P₂ t₁ o u (v₀ o) m h₁' t₂' h₂' hrest)

variable {s₁ s₂ P₁ P₂ v₀}

/-- **The serial loop is an exchange of the serial composition**: from a configuration where the
outer program has just answered (its turn) or the inner program has just answered (its turn),
the loop's outcome is the exchange's. -/
lemma serial_exchange {b₁ : ℕ} (hb : P₁.Bounded b₁) : ∀ n : ℕ,
    (∀ (G : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Y l))) (t₁ : S₁) (o : O)
        (u : U o) (h₁ : List ((Σ m, Xm m) × (Σ m, Ym m))) (t₂ : S₂),
      b₁ < n + h₁.length → P₁.Consistent t₁ o u h₁ →
      pair (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂) G =
        Part.some ⟨none, (P₁.emit t₁ o u h₁).2⟩ →
      P₁.after s₁ (restrict none G) = some (P₁.emit t₁ o u h₁).1 →
      P₂.after s₂ (restrict (some ()) G) = some (.idle t₂) →
      SerialOutcome s₁ s₂ P₁ P₂ v₀ n G t₁ o u h₁ t₂ []) ∧
    (∀ (G : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Y l))) (t₁ : S₁) (o : O)
        (u : U o) (h₁ : List ((Σ m, Xm m) × (Σ m, Ym m))) (q₁ : Σ m, Xm m) (t₂ : S₂)
        (h₂ : List ((Σ j, X j) × (Σ j, Y j))),
      b₁ < n + h₁.length → P₁.Consistent t₁ o u h₁ → P₁ t₁ o u h₁ = .inr q₁ →
      P₁.after s₁ (restrict none G) = some (.busy o t₁ u h₁ q₁) →
      pair (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂) G =
        Part.some ⟨some (), (P₂.emit t₂ q₁.1 q₁.2 h₂).2⟩ →
      P₂.after s₂ (restrict (some ()) G) = some (P₂.emit t₂ q₁.1 q₁.2 h₂).1 →
      SerialOutcome s₁ s₂ P₁ P₂ v₀ n G t₁ o u h₁ t₂ h₂) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun G t₁ o u h₁ t₂ hn hc => ?_, fun G t₁ o u h₁ q₁ t₂ h₂ hn hc => ?_⟩ <;>
      exact absurd (Consistent.length_le hb hc) (by omega)
  | succ n ih =>
    -- The inner program's turn, from the outer one's at `n`.
    have inner : ∀ (G : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Y l))) (t₁ : S₁)
        (o : O) (u : U o) (h₁ : List ((Σ m, Xm m) × (Σ m, Ym m))) (q₁ : Σ m, Xm m) (t₂ : S₂)
        (h₂ : List ((Σ j, X j) × (Σ j, Y j))),
        b₁ < n + 1 + h₁.length → P₁.Consistent t₁ o u h₁ → P₁ t₁ o u h₁ = .inr q₁ →
        P₁.after s₁ (restrict none G) = some (.busy o t₁ u h₁ q₁) →
        pair (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂) G =
          Part.some ⟨some (), (P₂.emit t₂ q₁.1 q₁.2 h₂).2⟩ →
        P₂.after s₂ (restrict (some ()) G) = some (P₂.emit t₂ q₁.1 q₁.2 h₂).1 →
        SerialOutcome s₁ s₂ P₁ P₂ v₀ (n + 1) G t₁ o u h₁ t₂ h₂ := by
      intro G t₁ o u h₁ q₁ t₂ h₂ hn hc h1 hm₁ hpair hm₂
      cases h2 : P₂ t₂ q₁.1 q₁.2 h₂ with
      | inl r =>
        obtain ⟨t₂', y⟩ := r
        have hemit : P₂.emit t₂ q₁.1 q₁.2 h₂ = (.idle t₂', ⟨⟨none, q₁.1⟩, y⟩) := by
          simp [emit, h2]
        rw [hemit] at hpair hm₂
        -- The reply goes back to the outer program, whose turn it is.
        set G' := G ++ [⟨none, ⟨⟨some (), q₁.1⟩, y⟩⟩]
        have hpair' : pair (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂) G' = Part.some
            ⟨none, (P₁.emit t₁ o u (h₁ ++ [(q₁, ⟨q₁.1, y⟩)])).2⟩ := by
          rw [pair_left, DDC.ofProgram_snoc, hm₁]
          simp [step]
        have hm₁' : P₁.after s₁ (restrict none G') =
            some (P₁.emit t₁ o u (h₁ ++ [(q₁, ⟨q₁.1, y⟩)])).1 := by
          rw [restrict_none_snoc_left, after_snoc, hm₁]
          simp [step]
        have hm₂' : P₂.after s₂ (restrict (some ()) G') = some (.idle t₂') := by
          rw [restrict_some_snoc_left, hm₂]
        obtain ⟨hl, hr⟩ := (ih.1 G' t₁ o u _ t₂' (by simp; omega) (hc.snoc h1 _) hpair' hm₁' hm₂')
        have hy : (⟨some (), ⟨⟨none, q₁.1⟩, y⟩⟩ : Two (Σ l, twoFam V Xm l) (Σ l, twoFam Ym X l)) ∈
            pair (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂) G := by
          rw [hpair]; exact Part.mem_some _
        rw [SerialOutcome, serialLoop_inner_return h1 h2]
        refine ⟨fun t₁' t₂'' v hv => ?_, fun q hq => ?_⟩
        · obtain ⟨G'', l, hG''⟩ := hl t₁' t₂'' v hv
          exact ⟨G'', Exchange.feed _ _ _ _ _ hy rfl l, hG''⟩
        · obtain ⟨G'', h₁', q₁', t₂'', h₂', k, l, hb₁, hb₂, hk, hrep⟩ := hr q hq
          refine ⟨G'', h₁', q₁', t₂'', h₂', k + 1, Exchange.feed _ _ _ _ _ hy rfl l, hb₁, hb₂,
            by simp at hk; omega, fun m hrest => ?_⟩
          rw [← Nat.add_assoc, serialLoop_inner_return h1 h2, hrep]
      | inr q₂ =>
        have hemit : P₂.emit t₂ q₁.1 q₁.2 h₂ =
            (.busy q₁.1 t₂ q₁.2 h₂ q₂, ⟨⟨some (), q₂.1⟩, q₂.2⟩) := by
          simp [emit, h2]
        rw [hemit] at hpair hm₂
        have hy : (⟨some (), ⟨⟨some (), q₂.1⟩, q₂.2⟩⟩ :
            Two (Σ l, twoFam V Xm l) (Σ l, twoFam Ym X l)) ∈
            pair (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂) G := by
          rw [hpair]; exact Part.mem_some _
        rw [SerialOutcome, serialLoop_query h1 h2]
        refine ⟨fun t₁' t₂' v hv => by simp at hv, fun q hq => ?_⟩
        obtain rfl : q₂ = q := by simpa using hq
        exact ⟨G, h₁, q₁, t₂, h₂, 0, Exchange.out _ _ _ hy rfl, hm₁, hm₂, rfl,
          fun m hrest => rfl⟩
    refine ⟨fun G t₁ o u h₁ t₂ hn hc hpair hm₁ hm₂ => ?_, inner⟩
    -- The outer program's turn.
    cases h1 : P₁ t₁ o u h₁ with
    | inl r =>
      obtain ⟨t₁', v⟩ := r
      have hemit : P₁.emit t₁ o u h₁ = (.idle t₁', ⟨⟨none, o⟩, v⟩) := by simp [emit, h1]
      rw [hemit] at hpair hm₁
      have hy : (⟨none, ⟨⟨none, o⟩, v⟩⟩ : Two (Σ l, twoFam V Xm l) (Σ l, twoFam Ym X l)) ∈
          pair (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂) G := by
        rw [hpair]; exact Part.mem_some _
      rw [SerialOutcome, serialLoop_return h1]
      refine ⟨fun t₁'' t₂' v' hv => ?_, fun q hq => by simp at hq⟩
      simp only [Sum.inl.injEq, Prod.mk.injEq] at hv
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hv
      exact ⟨G, Exchange.out _ _ _ hy rfl, hm₁, hm₂⟩
    | inr q₁ =>
      have hemit : P₁.emit t₁ o u h₁ = (.busy o t₁ u h₁ q₁, ⟨⟨some (), q₁.1⟩, q₁.2⟩) := by
        simp [emit, h1]
      rw [hemit] at hpair hm₁
      -- The query goes to the inner program, whose turn it is.
      set G' := G ++ [⟨some (), ⟨⟨none, q₁.1⟩, q₁.2⟩⟩]
      have hpair' : pair (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂) G' =
          Part.some ⟨some (), (P₂.emit t₂ q₁.1 q₁.2 []).2⟩ := by
        rw [pair_right, DDC.ofProgram_snoc, hm₂]
        simp [step]
      have hm₂' : P₂.after s₂ (restrict (some ()) G') = some (P₂.emit t₂ q₁.1 q₁.2 []).1 := by
        rw [restrict_some_snoc_right, after_snoc, hm₂]
        simp [step]
      have hm₁' : P₁.after s₁ (restrict none G') = some (.busy o t₁ u h₁ q₁) := by
        rw [restrict_none_snoc_right, hm₁]
      obtain ⟨hl, hr⟩ := inner G' t₁ o u h₁ q₁ t₂ [] hn hc h1 hm₁' hpair' hm₂'
      have hy : (⟨none, ⟨⟨some (), q₁.1⟩, q₁.2⟩⟩ :
          Two (Σ l, twoFam V Xm l) (Σ l, twoFam Ym X l)) ∈
          pair (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂) G := by
        rw [hpair]; exact Part.mem_some _
      refine ⟨fun t₁' t₂' v hv => ?_, fun q hq => ?_⟩
      · obtain ⟨G'', l, hG''⟩ := hl t₁' t₂' v hv
        exact ⟨G'', Exchange.feed _ _ _ _ _ hy rfl l, hG''⟩
      · obtain ⟨G'', h₁', q₁', t₂', h₂', k, l, rest⟩ := hr q hq
        exact ⟨G'', h₁', q₁', t₂', h₂', k, Exchange.feed _ _ _ _ _ hy rfl l, rest⟩

/-- An exchange with a reply starts from an answered internal history. -/
lemma _root_.SystemAlgebra.Exchange.dom_of_some {X' Y' B' : Type} {sys : System X' Y'}
    {route : Y' → B' ⊕ X'} {G G' : List X'} {w : B'} (l : Exchange sys route G (some w) G') :
    (sys G).Dom := by
  cases l with
  | out _ y _ hy _ => exact Part.dom_iff_mem.mpr ⟨y, hy⟩
  | feed _ y _ _ _ hy _ _ => exact Part.dom_iff_mem.mpr ⟨y, hy⟩

variable (s₁ s₂ P₁ P₂ v₀) in
/-- **The serial invariant**: an idle composed program holds the states of the two idle
programs; a busy one holds its invocation, from which the serial loop has reached the
configuration of the two waiting programs. -/
def SerialInv (b₁ : ℕ) (H : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Y l))) :
    Mode (S₁ × S₂) O J U X Y → Prop
  | .idle t => P₁.after s₁ (restrict none H) = some (.idle t.1) ∧
      P₂.after s₂ (restrict (some ()) H) = some (.idle t.2)
  | .busy o t u hc q => ∃ h₁ q₁ t₂ h₂,
      P₁.after s₁ (restrict none H) = some (.busy o t.1 u h₁ q₁) ∧
      P₂.after s₂ (restrict (some ()) H) = some (.busy q₁.1 t₂ q₁.2 h₂ q) ∧
      ∀ hrest, serialLoop P₁ P₂ t.1 o u (v₀ o) (b₁ + 1 + (hc ++ hrest).length) [] t.2 []
          (hc ++ hrest) =
        serialLoop P₁ P₂ t.1 o u (v₀ o) (b₁ + 1 - h₁.length + hrest.length) h₁ t₂ h₂ hrest

/-- **The serial composition of two programs' converters replies as the composed program.** -/
lemma replies_serial {b₁ : ℕ} (hb : P₁.Bounded b₁) :
    ∀ (xs : List (Σ l, twoFam U Y l)) (ys : List (Σ l, twoFam V X l)),
      Replies (serialM (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂)) xs ys →
      Replies (DDC.ofProgram (s₁, s₂) (P₁.serial P₂ b₁ v₀)) xs ys ∧
        ∃ o H m, Induces (pair (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂)) serialRouteM
            serialInjM xs o H ∧ (P₁.serial P₂ b₁ v₀).after (s₁, s₂) xs = some m ∧
          SerialInv s₁ s₂ P₁ P₂ v₀ b₁ H m := by
  intro xs
  induction xs using List.reverseRecOn with
  | nil =>
    intro ys hr
    obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hr.length
    exact ⟨replies_nil _, none, [], .idle (s₁, s₂), Induces.nil, rfl, rfl, rfl⟩
  | append_singleton xs x ih =>
    intro ys hr
    have hyn : ys ≠ [] := fun he => by have := hr.length; simp [he] at this
    obtain ⟨ys, y, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left hyn
    rw [List.concat_eq_append] at hr ⊢
    obtain ⟨hr₀, hy⟩ := replies_snoc.mp hr
    obtain ⟨hc₀, o, H, m, hi, hm, hinv⟩ := ih ys hr₀
    obtain ⟨H', hi'⟩ := mem_interconnect.mp (Part.eq_some_iff.mp hy)
    obtain ⟨o₀, H₀, hi₀, l⟩ := induces_snoc_iff.mp hi'
    obtain ⟨-, rfl⟩ := hi.det hi₀
    have hdom := l.dom_of_some
    -- The composed program's reply, and its mode, from the exchange.
    suffices key : ∃ m', (P₁.serial P₂ b₁ v₀).step m x = some (m', y) ∧
        SerialInv s₁ s₂ P₁ P₂ v₀ b₁ H' m' by
      obtain ⟨m', hs, hinv'⟩ := key
      refine ⟨replies_snoc.mpr ⟨hc₀, ?_⟩, some y, H', m', hi', ?_, hinv'⟩
      · rw [DDC.ofProgram_snoc, hm]
        simp [hs]
      · rw [after_snoc, hm]
        simp [hs]
    rcases m with ⟨t₁, t₂⟩ | ⟨o', ⟨t₁, t₂⟩, u', hc, q⟩ <;>
      rcases x with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, z⟩
    · -- Idle, an outside query: the outer program's turn on a new invocation.
      obtain ⟨hm₁, hm₂⟩ := hinv
      change Exchange _ _ (H ++ [⟨none, ⟨⟨none, j⟩, z⟩⟩]) _ _ at l
      have hpair : pair (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂)
          (H ++ [⟨none, ⟨⟨none, j⟩, z⟩⟩]) = Part.some ⟨none, (P₁.emit t₁ j z []).2⟩ := by
        rw [pair_left, DDC.ofProgram_snoc, hm₁]
        simp [step]
      have hm₁' : P₁.after s₁ (restrict none (H ++ [⟨none, ⟨⟨none, j⟩, z⟩⟩])) =
          some (P₁.emit t₁ j z []).1 := by
        rw [restrict_none_snoc_left, after_snoc, hm₁]
        simp [step]
      have hm₂' : P₂.after s₂ (restrict (some ()) (H ++ [⟨none, ⟨⟨none, j⟩, z⟩⟩])) =
          some (.idle t₂) := by
        rw [restrict_some_snoc_left, hm₂]
      obtain ⟨hl, hq⟩ := (serial_exchange (v₀ := v₀) hb (b₁ + 1)).1 _ t₁ j z [] t₂
        (by simp) (consistent_nil _ _ _ _) hpair hm₁' hm₂'
      have hstep : (P₁.serial P₂ b₁ v₀).step (.idle (t₁, t₂)) ⟨⟨none, j⟩, z⟩ =
          some ((P₁.serial P₂ b₁ v₀).emit (t₁, t₂) j z []) := rfl
      rw [hstep]
      cases hL : serialLoop P₁ P₂ t₁ j z (v₀ j) (b₁ + 1) [] t₂ [] [] with
      | inl r =>
        obtain ⟨⟨t₁', t₂'⟩, v⟩ := r
        obtain ⟨G'', l'', hG₁, hG₂⟩ := hl t₁' t₂' v hL
        obtain ⟨hy, rfl⟩ := l.det l''
        cases hy
        refine ⟨.idle (t₁', t₂'), ?_, hG₁, hG₂⟩
        simp [emit, serial, hL]
      | inr q =>
        obtain ⟨G'', h₁', q₁', t₂', h₂', k, l'', hG₁, hG₂, hk, hrep⟩ := hq q hL
        obtain ⟨hy, rfl⟩ := l.det l''
        cases hy
        refine ⟨.busy j (t₁, t₂) z [] q, by simp [emit, serial, hL], h₁', q₁', t₂', h₂', hG₁,
          hG₂, fun hrest => ?_⟩
        have hlt := hb _ _ _ _ _ (DDC.after_invariant hG₁).1.1 (DDC.after_invariant hG₁).1.2
        simp only [List.nil_append, List.length_nil] at hk ⊢
        rw [show b₁ + 1 + hrest.length = (b₁ + 1 - h₁'.length + hrest.length) + k by omega,
          hrep]
    · -- Idle, an inside reply: the inner program is silent.
      exfalso
      obtain ⟨-, hm₂⟩ := hinv
      change (pair (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂)
        (H ++ [⟨some (), ⟨⟨some (), j⟩, z⟩⟩])).Dom at hdom
      rw [pair_right, DDC.ofProgram_snoc, hm₂] at hdom
      simp [step] at hdom
    · -- Busy, an outside query: the outer program is silent.
      exfalso
      obtain ⟨h₁, q₁, t₂', h₂, hm₁, -⟩ := hinv
      change (pair (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂)
        (H ++ [⟨none, ⟨⟨none, j⟩, z⟩⟩])).Dom at hdom
      rw [pair_left, DDC.ofProgram_snoc, hm₁] at hdom
      simp [step] at hdom
    · -- Busy, an inside reply: the inner program's turn.
      obtain ⟨h₁, q₁, t₂', h₂, hm₁, hm₂, hrep⟩ := hinv
      by_cases hj : j = q.1
      swap
      · exfalso
        change (pair (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂)
          (H ++ [⟨some (), ⟨⟨some (), j⟩, z⟩⟩])).Dom at hdom
        rw [pair_right, DDC.ofProgram_snoc, hm₂] at hdom
        simp [step, hj] at hdom
      subst hj
      change Exchange _ _ (H ++ [⟨some (), ⟨⟨some (), q.1⟩, z⟩⟩]) _ _ at l
      obtain ⟨hc₁, h1⟩ := (DDC.after_invariant hm₁).1
      obtain ⟨-, h2⟩ := (DDC.after_invariant hm₂).1
      have hlt := hb _ _ _ _ _ hc₁ h1
      have hpair : pair (DDC.ofProgram s₁ P₁) (DDC.ofProgram s₂ P₂)
          (H ++ [⟨some (), ⟨⟨some (), q.1⟩, z⟩⟩]) =
            Part.some ⟨some (), (P₂.emit t₂' q₁.1 q₁.2 (h₂ ++ [(q, ⟨q.1, z⟩)])).2⟩ := by
        rw [pair_right, DDC.ofProgram_snoc, hm₂]
        simp [step]
      have hm₂' : P₂.after s₂ (restrict (some ()) (H ++ [⟨some (), ⟨⟨some (), q.1⟩, z⟩⟩])) =
          some (P₂.emit t₂' q₁.1 q₁.2 (h₂ ++ [(q, ⟨q.1, z⟩)])).1 := by
        rw [restrict_some_snoc_right, after_snoc, hm₂]
        simp [step]
      have hm₁' : P₁.after s₁ (restrict none (H ++ [⟨some (), ⟨⟨some (), q.1⟩, z⟩⟩])) =
          some (.busy o' t₁ u' h₁ q₁) := by
        rw [restrict_none_snoc_right, hm₁]
      obtain ⟨hl, hq⟩ := (serial_exchange (v₀ := v₀) hb (b₁ + 1 - h₁.length)).2 _ t₁ o' u' h₁ q₁
        t₂' _ (by omega) hc₁ h1 hm₁' hpair hm₂'
      have hstep : (P₁.serial P₂ b₁ v₀).step (.busy o' (t₁, t₂) u' hc q) ⟨⟨some (), q.1⟩, z⟩ =
          some ((P₁.serial P₂ b₁ v₀).emit (t₁, t₂) o' u' (hc ++ [(q, ⟨q.1, z⟩)])) := by
        simp [step]
      -- The composed body replays its invocation to the two waiting programs, then feeds the
      -- reply.
      have hbody : (P₁.serial P₂ b₁ v₀) (t₁, t₂) o' u' (hc ++ [(q, ⟨q.1, z⟩)]) =
          serialLoop P₁ P₂ t₁ o' u' (v₀ o') (b₁ + 1 - h₁.length) h₁ t₂' (h₂ ++ [(q, ⟨q.1, z⟩)])
            [] := by
        change serialLoop P₁ P₂ t₁ o' u' (v₀ o') _ [] t₂ [] _ = _
        rw [hrep [(q, ⟨q.1, z⟩)], List.length_singleton, serialLoop_feed h1 h2]
      rw [hstep]
      cases hL : serialLoop P₁ P₂ t₁ o' u' (v₀ o') (b₁ + 1 - h₁.length) h₁ t₂'
          (h₂ ++ [(q, ⟨q.1, z⟩)]) [] with
      | inl r =>
        obtain ⟨⟨t₁', t₂''⟩, v⟩ := r
        obtain ⟨G'', l'', hG₁, hG₂⟩ := hl t₁' t₂'' v hL
        obtain ⟨hy, rfl⟩ := l.det l''
        cases hy
        refine ⟨.idle (t₁', t₂''), ?_, hG₁, hG₂⟩
        simp [emit, hbody, hL]
      | inr q' =>
        obtain ⟨G'', h₁', q₁', t₂'', h₂', k, l'', hG₁, hG₂, hk, hrep'⟩ := hq q' hL
        obtain ⟨hy, rfl⟩ := l.det l''
        cases hy
        refine ⟨.busy o' (t₁, t₂) u' (hc ++ [(q, ⟨q.1, z⟩)]) q', by simp [emit, hbody, hL],
          h₁', q₁', t₂'', h₂', hG₁, hG₂, fun hrest => ?_⟩
        have hlt' := hb _ _ _ _ _ (DDC.after_invariant hG₁).1.1 (DDC.after_invariant hG₁).1.2
        dsimp only
        rw [List.append_assoc, List.singleton_append, hrep, List.length_cons,
          ← Nat.add_assoc, serialLoop_feed h1 h2,
          show b₁ + 1 - h₁.length + hrest.length = (b₁ + 1 - h₁'.length + hrest.length) + k by
            omega, hrep']

end Exchange

end Program

namespace DDC

variable {S S' O J : Type} {U V : O → Type} {X Y : J → Type}

/-- **Bisimilar programs have the same converter**: if, from related states, on every exchange
the first body makes itself, the second queries as the first does and replies as it does into a
related state, the two programs are one converter. -/
lemma ofProgram_eq_of_bisim {P : Program S O J U V X Y} {P' : Program S' O J U V X Y}
    (rel : S → S' → Prop) {s : S} {s' : S'} (hs : rel s s')
    (hP : ∀ t t', rel t t' → ∀ o u h, P.Consistent t o u h →
      (∀ q, P t o u h = .inr q → P' t' o u h = .inr q) ∧
      (∀ t₁ v, P t o u h = .inl (t₁, v) → ∃ t₁', P' t' o u h = .inl (t₁', v) ∧ rel t₁ t₁')) :
    DDC.ofProgram s P = DDC.ofProgram s' P' := by
  -- The modes after a history are related.
  let modeRel : Program.Mode S O J U X Y → Program.Mode S' O J U X Y → Prop
    | .idle t, .idle t' => rel t t'
    | .busy o t u h q, .busy o' t' u' h' q' =>
      ∃ e : o = o', rel t t' ∧ e ▸ u = u' ∧ h = h' ∧ q = q' ∧ P.Consistent t o u h ∧
        P t o u h = .inr q
    | _, _ => False
  have hemit : ∀ t t' o u h, rel t t' → P.Consistent t o u h →
      (P.emit t o u h).2 = (P'.emit t' o u h).2 ∧
        modeRel (P.emit t o u h).1 (P'.emit t' o u h).1 := by
    intro t t' o u h ht hc
    obtain ⟨hq, hl⟩ := hP t t' ht o u h hc
    cases hPt : P t o u h with
    | inl r =>
      obtain ⟨t₁, v⟩ := r
      obtain ⟨t₁', hP', hr⟩ := hl t₁ v hPt
      have e₁ : P.emit t o u h = (.idle t₁, ⟨⟨none, o⟩, v⟩) := by simp [Program.emit, hPt]
      have e₂ : P'.emit t' o u h = (.idle t₁', ⟨⟨none, o⟩, v⟩) := by simp [Program.emit, hP']
      rw [e₁, e₂]
      exact ⟨rfl, hr⟩
    | inr q =>
      have e₁ : P.emit t o u h = (.busy o t u h q, ⟨⟨some (), q.1⟩, q.2⟩) := by
        simp [Program.emit, hPt]
      have e₂ : P'.emit t' o u h = (.busy o t' u h q, ⟨⟨some (), q.1⟩, q.2⟩) := by
        simp [Program.emit, hq q hPt]
      rw [e₁, e₂]
      exact ⟨rfl, rfl, ht, rfl, rfl, rfl, hc, hPt⟩
  have hstep : ∀ m m' x, modeRel m m' →
      (P.step m x = none ∧ P'.step m' x = none) ∨
        ∃ n n' y, P.step m x = some (n, y) ∧ P'.step m' x = some (n', y) ∧ modeRel n n' := by
    intro m m' x hm
    rcases m with t | ⟨o, t, u, h, q⟩ <;> rcases m' with t' | ⟨o', t', u', h', q'⟩ <;>
      try exact absurd hm id
    · rcases x with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, u⟩
      · obtain ⟨he, hr⟩ := hemit t t' o u [] hm (Program.consistent_nil _ _ _ _)
        refine Or.inr ⟨(P.emit t o u []).1, (P'.emit t' o u []).1, (P.emit t o u []).2, rfl, ?_,
          hr⟩
        change some (P'.emit t' o u []) = some ((P'.emit t' o u []).1, (P.emit t o u []).2)
        rw [he]
      · exact Or.inl ⟨rfl, rfl⟩
    · obtain ⟨rfl, ht, rfl, rfl, rfl, hc, hq⟩ := hm
      rcases x with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, y⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · by_cases hj : j = q.1
        · subst hj
          obtain ⟨he, hr⟩ := hemit t t' o u (h ++ [(q, ⟨q.1, y⟩)]) ht (hc.snoc hq y)
          refine Or.inr ⟨(P.emit t o u (h ++ [(q, ⟨q.1, y⟩)])).1,
            (P'.emit t' o u (h ++ [(q, ⟨q.1, y⟩)])).1, (P.emit t o u (h ++ [(q, ⟨q.1, y⟩)])).2,
            by simp [Program.step], ?_, hr⟩
          rw [he]
          simp [Program.step]
        · exact Or.inl ⟨by simp [Program.step, hj], by simp [Program.step, hj]⟩
  have after : ∀ xs, (P.after s xs = none ∧ P'.after s' xs = none) ∨
      ∃ m m', P.after s xs = some m ∧ P'.after s' xs = some m' ∧ modeRel m m' := by
    intro xs
    induction xs using List.reverseRecOn with
    | nil => exact Or.inr ⟨_, _, rfl, rfl, hs⟩
    | append_singleton xs x ih =>
      rw [Program.after_snoc, Program.after_snoc]
      rcases ih with ⟨h₁, h₂⟩ | ⟨m, m', h₁, h₂, hm⟩
      · exact Or.inl ⟨by rw [h₁]; rfl, by rw [h₂]; rfl⟩
      · rw [h₁, h₂]
        rcases hstep m m' x hm with ⟨e₁, e₂⟩ | ⟨n, n', y, e₁, e₂, hn⟩
        · exact Or.inl ⟨by simp [e₁], by simp [e₂]⟩
        · exact Or.inr ⟨n, n', by simp [e₁], by simp [e₂], hn⟩
  funext xs
  rcases List.eq_nil_or_concat xs with rfl | ⟨xs, x, rfl⟩
  · rfl
  · rw [List.concat_eq_append, ofProgram_snoc, ofProgram_snoc]
    rcases after xs with ⟨h₁, h₂⟩ | ⟨m, m', h₁, h₂, hm⟩
    · rw [h₁, h₂]; rfl
    · rw [h₁, h₂]
      rcases hstep m m' x hm with ⟨e₁, e₂⟩ | ⟨n, n', y, e₁, e₂, -⟩
      · simp [e₁, e₂]
      · simp [e₁, e₂]

end DDC

namespace Interface

/-- **The serial composition of two program converters is the converter of the composed
program**: it is every converter between the outer and the innermost domains replying as the
composed program, the converter of the composed program on the outer domain for one. -/
lemma ofDDC_ofProgramOn_comp {A B C : Interface} {S₁ S₂ : Type} (s₁ : S₁)
    (P₁ : Program S₁ A.I B.I A.X A.Y B.X B.Y) {b₁ : ℕ} (hb₁ : P₁.Bounded b₁)
    (h₁ : IsDDCFrom B.domain A.domain b₁ (DDC.ofProgramOn s₁ P₁ A.domain)) (s₂ : S₂)
    (P₂ : Program S₂ B.I C.I B.X B.Y C.X C.Y) {b₂ : ℕ}
    (h₂ : IsDDCFrom C.domain B.domain b₂ (DDC.ofProgramOn s₂ P₂ B.domain))
    (v₀ : ∀ o, A.Y o) {d : InsideOutsideSystem A.I C.I A.X A.Y C.X C.Y} {b : ℕ}
    (hd : IsDDCFrom C.domain A.domain b d)
    (replies : ∀ xs ys, Replies d xs ys →
      Replies (DDC.ofProgram (s₁, s₂) (P₁.serial P₂ b₁ v₀)) xs ys) :
    Interface.ofDDC (DDC.ofProgramOn s₁ P₁ A.domain) h₁ ≫
        Interface.ofDDC (DDC.ofProgramOn s₂ P₂ B.domain) h₂ = Interface.ofDDC d hd := by
  rw [Interface.comp_eq]
  refine (PDCBehavior.comp_ofDDC h₁ h₂).trans ?_
  have hsub : ∀ {S O J : Type} {U V : O → Type} {X Y : J → Type} (s : S)
      (P : Program S O J U V X Y) (F : List (Σ o, U o) → Prop) h y,
      y ∈ DDC.ofProgramOn s P F h → y ∈ DDC.ofProgram s P h :=
    fun _ _ _ h y hy => ((filterDom_mem_iff _ _ h y).mp hy).2
  refine PDCBehavior.ofDDC_eq_of_le _ _ (W := DDC.ofProgram (s₁, s₂) (P₁.serial P₂ b₁ v₀))
    (fun xs ys hr => ?_) replies
  rw [replies_trim_iff] at hr
  exact (Program.replies_serial hb₁ xs ys
    (Replies.interconnect_mono (pair_mono (hsub _ _ _) (hsub _ _ _)) hr)).1

end Interface

end Serial

end SystemAlgebra
