import Probability.Distribution
import Probability.Counting

/-!
# Composite laws and collision bounds

Upstream candidates for `Probability.Distribution`. Component bodies sample from closed laws, so
an algorithm whose law depends on its inputs is sampled through the law of its runs on every
input, and running one probabilistic algorithm on the output of another is a law of its own.

The collision bounds of the sampled-function games are union bounds: over the pairs of distinct
elements of a finite set, for a symmetric family of events, and two distinct points of a uniform
function agree with probability at most `1/|X|`. Their game equivalences rest on the values of a
uniform function at distinct points being uniform, also at points that are fresh for a condition
on the function elsewhere, and on the values of a uniform permutation at distinct points forming
each injection with the same probability. Re-indexing a sample by a map that keeps its law, at
one coordinate of independent samples or at the second of a pair for every first, keeps the law.
Upstream candidates for `Probability.Distribution` (`Distribution.ProbDist.fTransform_eval_pi`,
`Distribution.mass_exists_pair_le`, `Distribution.pi_uniform`,
`Distribution.fTransform_pi_comp_injective`, `Distribution.fTransform_update_pi`,
`Distribution.fTransform_prod_fiber_map`, `Distribution.fTransform_prod_fiber`,
`Distribution.fTransform_update_uniform`, `Distribution.fTransform_pi_map`,
`Distribution.fTransform_prod_fiber_apply`, `Distribution.fTransform_val_uniform`,
`Distribution.fTransform_val_uniform_apply`, `Distribution.sum_eq_one`, `natCast_mul_sub_one_le`)
and `Probability.Counting` (`Counting.uniform_mass_apply_eq_le`,
`Counting.uniform_mass_apply_list_eq`, `Counting.uniform_mass_fresh_eq`,
`Counting.uniform_perm_mass_eq`, `Counting.uniform_perm_mass_eq_inv`).

## Main definitions

* `Distribution.ProbDist.map f P`: the law of `f a` for `a ← P`
* `Distribution.ProbDist.pi μ`: independent samples of `μ i` for every `i`
* `Distribution.ProbDist.bind P f`: the law of `b ← f a` for `a ← P`

## Main results

* `Distribution.ProbDist.map_map`: pushing forward twice is pushing forward along the composite
* `Distribution.ProbDist.mem_support_map`, `Distribution.ProbDist.mem_support_pi`,
  `Distribution.ProbDist.mem_support_bind`: the possible outcomes of the composite laws
* `Distribution.ProbDist.fTransform_eval_pi`: a coordinate of independent samples
* `Distribution.mass_exists_pair_le`: the union bound over pairs
* `Counting.uniform_mass_apply_eq_le`: two distinct points of a uniform function agree with
  probability at most `1/|X|`
* `Counting.uniform_mass_apply_list_eq`, `Counting.uniform_mass_fresh_eq`: the values of a
  uniform function at distinct points, and at fresh points
* `Counting.uniform_perm_mass_eq`, `Counting.uniform_perm_mass_eq_inv`: the values of a uniform
  permutation at distinct points
* `Distribution.pi_uniform`: independent uniform samples are a uniform function
* `Distribution.fTransform_pi_comp_injective`: independent samples read along an injection
* `Distribution.fTransform_update_pi`, `Distribution.fTransform_prod_fiber_map`,
  `Distribution.fTransform_prod_fiber`: re-indexing one coordinate, and the second of a pair
  fiberwise, along maps keeping the law
* `Distribution.fTransform_update_uniform`: a uniform function updated with a uniform value
* `Distribution.fTransform_pi_map`, `Distribution.fTransform_prod_fiber_apply`: independent
  samples mapped coordinatewise, and the mass of a fiberwise pushforward of a pair
* `Distribution.fTransform_val_uniform`, `Distribution.fTransform_val_uniform_apply`: the
  uniform law on a set, kept by a permutation of the set, and its masses
* `natCast_mul_sub_one_le`: `s(cs-1) ≤ q(cq-1)` for `s ≤ q` and `c ≥ 1`
-/

namespace Probability.Distribution.ProbDist

variable {A B ι : Type*}

/-- **The pushforward** of a law: the law of `f a` for `a ← P`. -/
noncomputable def map (f : A → B) (P : ProbDist A) : ProbDist B :=
  ⟨fTransform f P.1, fTransform_isProbDist f P.2⟩

/-- **Pushing forward twice** is pushing forward along the composite. -/
lemma map_map {C : Type*} (f : B → C) (g : A → B) (P : ProbDist A) :
    map f (map g P) = map (f ∘ g) P :=
  -- Both sides have the same underlying distribution: `fTransform f ∘ fTransform g`.
  Subtype.ext (fTransform_fTransform _ _ _)

/-- **Independent samples** of `μ i` at every index `i` of a finite type. -/
noncomputable def pi [Fintype ι] [DecidableEq ι] (μ : ι → ProbDist A) : ProbDist (ι → A) :=
  ⟨Distribution.pi fun i => (μ i).1, pi_isProbDist fun i => (μ i).2⟩

/-- **Sequential composition**: the law of `b ← f a` for `a ← P`, as the sample at `a` of
independent samples of `f` at every point. -/
noncomputable def bind [Fintype A] [DecidableEq A] (P : ProbDist A) (f : A → ProbDist B) :
    ProbDist B :=
  map (fun x => x.2 x.1) (prodProbDist P (pi f))

/-- A possible outcome of the pushforward is the image of a possible outcome. -/
lemma mem_support_map {f : A → B} {P : ProbDist A} {b : B} (hb : b ∈ (map f P).1.support) :
    ∃ a ∈ P.1.support, f a = b :=
  mem_support_fTransform f P.1 hb

/-- A possible outcome of independent samples is possible at every index. -/
lemma mem_support_pi [Fintype ι] [DecidableEq ι] {μ : ι → ProbDist A} {g : ι → A}
    (hg : g ∈ (pi μ).1.support) (i : ι) : g i ∈ (μ i).1.support := by
  rw [Finsupp.mem_support_iff] at hg ⊢
  change Distribution.pi (fun i => (μ i).1) g ≠ 0 at hg
  rw [Distribution.pi_apply] at hg
  exact fun h => hg (Finset.prod_eq_zero (Finset.mem_univ i) h)

/-- A possible outcome of `b ← f a` for `a ← P` is a possible outcome of `f a` for a possible
`a`. -/
lemma mem_support_bind [Fintype A] [DecidableEq A] {P : ProbDist A} {f : A → ProbDist B}
    {b : B} (hb : b ∈ (bind P f).1.support) : ∃ a ∈ P.1.support, b ∈ (f a).1.support := by
  obtain ⟨⟨a, g⟩, hag, rfl⟩ := mem_support_map hb
  have hmem := Finset.mem_product.mp (Distribution.support_prod_subset _ _ hag)
  exact ⟨a, hmem.1, mem_support_pi hmem.2 a⟩

/-- **A coordinate of independent samples** has the law of its index. -/
lemma fTransform_eval_pi [Fintype ι] [DecidableEq ι] (μ : ι → ProbDist A) (i : ι) :
    fTransform (fun t => t i) (ProbDist.pi μ).1 = (μ i).1 := by
  change marginalAt (Distribution.pi fun i => (μ i).1) i = _
  rw [marginalAt_pi, Finset.prod_eq_one fun j _ => (μ j).2.2, one_smul]

end Probability.Distribution.ProbDist

namespace Probability

/-- **The union bound over pairs**: if the events `E i j` are symmetric and each of mass at most
`c` for distinct `i, j ∈ s`, two distinct elements of `s` satisfy `E` with mass at most
`|s|(|s|-1)/2 · c`. -/
lemma Distribution.mass_exists_pair_le {A ι : Type*} [DecidableEq ι] {X : Distribution A}
    (hX : X.NonNeg) (s : Finset ι) (E : ι → ι → A → Prop) (symm : ∀ i j a, E i j a → E j i a)
    {c : ℝ} (bound : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → X.mass (E i j) ≤ c) :
    X.mass (fun a => ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ E i j a) ≤ s.card * (s.card - 1) / 2 * c := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Distribution.mass_eq_zero_of_forall_not X (by simp)]
    simp
  | insert a t ha ih =>
    -- A new pair involves the new element `a` and one of the `|t|` others.
    have step : ∀ x, (∃ i ∈ insert a t, ∃ j ∈ insert a t, i ≠ j ∧ E i j x) →
        (∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ E i j x) ∨ ∃ j ∈ t, E a j x := by
      rintro x ⟨i, hi, j, hj, hij, he⟩
      rw [Finset.mem_insert] at hi hj
      by_cases hia : i = a
      · subst hia
        exact Or.inr ⟨j, hj.resolve_left (Ne.symm hij), he⟩
      · by_cases hja : j = a
        · subst hja
          exact Or.inr ⟨i, hi.resolve_left hia, symm _ _ _ he⟩
        · exact Or.inl ⟨i, hi.resolve_left hia, j, hj.resolve_left hja, hij, he⟩
    have hih := ih fun i hi j hj hij => bound i (Finset.mem_insert_of_mem hi) j
      (Finset.mem_insert_of_mem hj) hij
    have hnew : X.mass (fun x => ∃ j ∈ t, E a j x) ≤ t.card * c := by
      refine (Distribution.mass_exists_le hX t _).trans ?_
      refine (Finset.sum_le_sum fun j hj => bound a (Finset.mem_insert_self a t) j
        (Finset.mem_insert_of_mem hj) (fun h => ha (h ▸ hj))).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    refine ((Distribution.mass_mono hX step).trans (Distribution.mass_or_le hX _ _)).trans
      ((add_le_add hih hnew).trans (le_of_eq ?_))
    rw [Finset.card_insert_of_notMem ha]
    push_cast
    ring

/-- **Two distinct points of a uniform function agree** with probability at most `1/|X|`. -/
lemma Counting.uniform_mass_apply_eq_le {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]
    [DecidableEq X] [Nonempty X] {i j : ι} (h : i ≠ j) :
    (Distribution.uniform (ι → X)).mass (fun T => T i = T j) ≤ 1 / Fintype.card X :=
  Counting.uniform_mass_coord_determined_le i id Function.injective_id (fun T => T j)
    fun _ _ hT => hT j (Ne.symm h)

/-- **Values of a uniform function at distinct points**: at the images of a list under a map
injective on it, a uniform function takes prescribed values with probability `|Y|^{-n}`, for `n`
the number of distinct elements of the list. -/
lemma Counting.uniform_mass_apply_list_eq {X X' Y : Type*} [DecidableEq X] [Fintype X']
    [DecidableEq X'] [Fintype Y] [DecidableEq Y] [Nonempty Y] (xs : List X) (p : X → X')
    (hp : Set.InjOn p xs.toFinset) (a : X → Y) :
    (Distribution.uniform (X' → Y)).mass (fun g => ∀ x ∈ xs, g (p x) = a x) =
      (1 / (Fintype.card Y : ℝ)) ^ xs.toFinset.card := by
  rw [← Fintype.card_coe xs.toFinset, ← Counting.uniform_mass_eval_eq (X := X') (Y := Y)
    (fun i : xs.toFinset => p i.1) (fun i j h => Subtype.ext (hp i.2 j.2 h)) (fun i => a i.1)]
  refine Distribution.mass_congr _ fun g => ⟨fun h => funext fun i => h i.1
    (List.mem_toFinset.mp i.2), fun h x hx => congrFun h ⟨x, List.mem_toFinset.mpr hx⟩⟩

/-- **Values of a uniform function at fresh points**: if a condition `Good` and points `u T`
depend only on `T` on a set `S`, and under `Good` the points are distinct and outside `S`, then
`T` takes prescribed values at its points, jointly with `Good`, with probability `|Y|^{-|ι|}`
times that of `Good`. Shifting `T` at its points is a free action on the functions of `Good`
that shifts the values there. -/
lemma Counting.uniform_mass_fresh_eq {X Y ι : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Nonempty Y] [Fintype ι] [DecidableEq ι]
    (S : Set X) (Good : (X → Y) → Prop) (u : (X → Y) → ι → X)
    (local_good : ∀ T T', (∀ x ∈ S, T x = T' x) → (Good T ↔ Good T'))
    (local_u : ∀ T T', (∀ x ∈ S, T x = T' x) → u T = u T')
    (fresh : ∀ T, Good T → Function.Injective (u T) ∧ ∀ i, u T i ∉ S) (c : ι → Y) :
    (Distribution.uniform (X → Y)).mass (fun T => (fun i => T (u T i)) = c ∧ Good T) =
      (1 / (Fintype.card Y : ℝ)) ^ Fintype.card ι * (Distribution.uniform (X → Y)).mass Good := by
  classical
  have keep : ∀ (δ : ι → Y) T, Good T → ∀ x ∈ S, Counting.multiShift (u T) δ T x = T x :=
    fun δ T hT x hx => Counting.multiShift_apply_of_ne δ T fun i h => (fresh T hT).2 i (h ▸ hx)
  have count := Counting.card_filter_shift_univ (A := ι → Y) Good (fun T i => T (u T i))
    (fun δ T => Counting.multiShift (u T) δ T)
    (fun δ T hT => (local_good _ _ (keep δ T hT)).mpr hT)
    (fun δ T hT => by
      funext i
      rw [local_u _ _ (keep δ T hT), Counting.multiShift_apply_site δ T (fresh T hT).1]
      rfl)
    (fun δ δ' T hT => by
      rw [local_u _ _ (keep δ T hT), Counting.multiShift_multiShift])
    (fun T _ => Counting.multiShift_zero _ T) c
  rw [Distribution.uniform_mass_eq_card_filter, Distribution.uniform_mass_eq_card_filter,
    ← count, Fintype.card_fun]
  push_cast
  rw [div_pow, one_pow]
  have hY : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  field_simp
  rw [Fintype.card_fun]
  push_cast
  ring

/-- **The values of a uniform permutation at the points of an embedding** form every embedding
with the same probability: permutations act transitively on embeddings. -/
lemma Counting.uniform_perm_mass_eq {X ι : Type*} [Fintype X] [DecidableEq X] [Fintype ι]
    (p a b : ι ↪ X) :
    (Distribution.uniform (Equiv.Perm X)).mass (fun σ => ∀ i, σ (p i) = a i) =
      (Distribution.uniform (Equiv.Perm X)).mass (fun σ => ∀ i, σ (p i) = b i) := by
  classical
  -- A permutation `τ` with `τ ∘ a = b`.
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm X, ∀ i, τ (a i) = b i := by
    let e := Fintype.equivFin ι
    have := (MulAction.isMultiplyPretransitive_iff (G := Equiv.Perm X) (α := X)
      (n := Fintype.card ι)).mp (Equiv.Perm.isMultiplyPretransitive X _)
      (e.symm.toEmbedding.trans a) (e.symm.toEmbedding.trans b)
    obtain ⟨τ, h⟩ := this
    refine ⟨τ, fun i => ?_⟩
    have := congrArg (fun f : Fin _ ↪ X => f (e i)) h
    simpa using this
  conv_rhs => rw [← Distribution.fTransform_equiv_uniform (Equiv.mulLeft τ),
    Distribution.mass_fTransform]
  refine Distribution.mass_congr _ fun σ => ?_
  simp only [Equiv.coe_mulLeft, Equiv.Perm.coe_mul, Function.comp_apply]
  constructor
  · intro h i
    rw [h i, hτ]
  · intro h i
    have := h i
    rw [← hτ] at this
    exact τ.injective this

/-- **The values of a uniform permutation at the points of an embedding** form each embedding
with probability `1/|ι ↪ X|`. -/
lemma Counting.uniform_perm_mass_eq_inv {X ι : Type*} [Fintype X] [DecidableEq X] [Fintype ι]
    [DecidableEq ι] (p a : ι ↪ X) :
    (Distribution.uniform (Equiv.Perm X)).mass (fun σ => ∀ i, σ (p i) = a i) =
      1 / Fintype.card (ι ↪ X) := by
  classical
  have total := Distribution.mass_eq_sum_mass_fiber (Distribution.uniform (Equiv.Perm X))
    (fun _ => True) (fun σ => p.trans σ.toEmbedding) Finset.univ (fun _ _ => Finset.mem_univ _)
  rw [Distribution.mass_true, Distribution.weight_uniform] at total
  have each : ∀ b : ι ↪ X, (Distribution.uniform (Equiv.Perm X)).mass
      (fun σ => True ∧ p.trans σ.toEmbedding = b) =
      (Distribution.uniform (Equiv.Perm X)).mass (fun σ => ∀ i, σ (p i) = a i) := by
    intro b
    rw [Counting.uniform_perm_mass_eq p a b]
    refine Distribution.mass_congr _ fun σ => ?_
    simp [Function.Embedding.ext_iff]
  simp only [each, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at total
  have hc : (0 : ℝ) < Fintype.card (ι ↪ X) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨a⟩
  field_simp
  linarith

/-- **Independent uniform samples** are a uniform function. -/
lemma Distribution.pi_uniform {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    [Nonempty A] [DecidableEq A] :
    Distribution.pi (fun _ : ι => Distribution.uniform A) = Distribution.uniform (ι → A) := by
  ext f
  rw [Distribution.pi_apply, Distribution.uniform_apply]
  simp [Distribution.uniform_apply]

/-- **Independent samples read along an injection** are independent samples: if `t` is a family
of independent samples of `μ`, so is `t ∘ e` for an injective `e`. -/
lemma Distribution.fTransform_pi_comp_injective {ι ι' A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] [Fintype A] [DecidableEq A] (μ : Distribution A)
    (hμ : μ.weight = 1) (e : ι' → ι) (he : Function.Injective e) :
    Distribution.fTransform (fun t : ι → A => t ∘ e) (Distribution.pi fun _ : ι => μ) =
      Distribution.pi fun _ : ι' => μ := by
  classical
  ext f
  -- The values at the images of a finite set, one point at a time.
  have points : ∀ s : Finset ι', (Distribution.pi fun _ : ι => μ).mass
      (fun t => ∀ i ∈ s, t (e i) = f i) = ∏ i ∈ s, μ (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, false_implies, implies_true, Finset.prod_empty]
      rw [Distribution.mass_true, Distribution.weight_pi]
      simp [hμ]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, ← ih, mul_comm]
      rw [Distribution.mass_congr _ (Q := fun t => (∀ i ∈ s, t (e i) = f i) ∧ t (e a) = f a)
        fun t => by simp only [Finset.mem_insert, forall_eq_or_imp]; tauto]
      refine Distribution.mass_pi_and_eq _ (fun _ => hμ) (e a) (f a) _ fun t b => ?_
      refine forall₂_congr fun i hi => ?_
      rw [Function.update_of_ne fun h : e i = e a => ha (he h ▸ hi)]
  rw [Distribution.fTransform_apply_eq_mass, Distribution.pi_apply]
  refine (Distribution.mass_congr _ (Q := fun t : ι → A => ∀ i ∈ Finset.univ, t (e i) = f i)
    fun t => ⟨fun h i _ => congrFun h i, fun h => funext fun i => h i (Finset.mem_univ i)⟩).trans
    (points Finset.univ)

/-- **Updating one coordinate** of independent samples along a map that keeps its law keeps the
law of the samples. -/
lemma Distribution.fTransform_update_pi {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq A] (μ : ι → Distribution A) (i : ι) (f : A → A)
    (hf : Distribution.fTransform f (μ i) = μ i) :
    Distribution.fTransform (fun g => Function.update g i (f (g i))) (Distribution.pi μ) =
      Distribution.pi μ := by
  classical
  ext g
  rw [Distribution.fTransform_apply_eq_mass, Distribution.mass_eq_sum, Distribution.pi_apply]
  -- The histories mapped to `g` are `g` updated at `i` by a preimage of `g i` under `f`.
  have key : ∀ g' : ι → A, (Function.update g' i (f (g' i)) = g) ↔
      ∃ a, f a = g i ∧ g' = Function.update g i a := by
    intro g'
    constructor
    · intro h
      refine ⟨g' i, by rw [← h, Function.update_self], ?_⟩
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj, ← h, Function.update_of_ne hj]
    · rintro ⟨a, ha, rfl⟩
      funext j
      by_cases hj : j = i
      · subst hj; simp [ha]
      · simp [Function.update_of_ne hj]
  have hsum : (∑ g' : ι → A,
      if Function.update g' i (f (g' i)) = g then Distribution.pi μ g' else 0) =
      ∑ g' ∈ Finset.univ.filter (fun g' : ι → A => Function.update g' i (f (g' i)) = g),
        Distribution.pi μ g' := by
    rw [Finset.sum_filter]
  refine (Eq.trans ?_ hsum).trans ?_
  · exact Finset.sum_congr rfl fun g' _ => by congr
  have hS : Finset.univ.filter (fun g' : ι → A => Function.update g' i (f (g' i)) = g) =
      (Finset.univ.filter (fun a => f a = g i)).image (fun a => Function.update g i a) := by
    ext g'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, key]
    exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h.symm⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h.symm⟩⟩
  rw [hS, Finset.sum_image (fun a _ b _ h => by simpa using congrFun h i)]
  have point : ∀ a, Distribution.pi μ (Function.update g i a) =
      μ i a * ∏ j ∈ Finset.univ.erase i, μ j (g j) := by
    intro a
    rw [Distribution.pi_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  simp only [point]
  rw [← Finset.sum_mul]
  have hm : ∑ a ∈ Finset.univ.filter (fun a => f a = g i), μ i a = μ i (g i) := by
    conv_rhs => rw [← hf, Distribution.fTransform_apply_eq_mass, Distribution.mass_eq_sum]
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun a _ => by congr
  rw [hm, Finset.mul_prod_erase _ (fun j => μ j (g j)) (Finset.mem_univ i)]

/-- **A fiberwise pushforward** of an independent pair, into another law: moving the second
sample along a map that depends on the first, and takes the law of the second to `Q'` for every
possible first, gives the independent pair with `Q'`. -/
lemma Distribution.fTransform_prod_fiber_map {A B B' : Type} (P : Distribution A)
    (Q : Distribution B) (Q' : Distribution B') (g : A → B → B')
    (hg : ∀ a ∈ P.support, Distribution.fTransform (g a) Q = Q') :
    Distribution.fTransform (fun p => (p.1, g p.1 p.2)) (Distribution.prod P Q) =
      Distribution.prod P Q' := by
  classical
  ext ⟨a, b⟩
  rw [Distribution.fTransform_apply_eq_mass, Distribution.prod_apply]
  rw [Distribution.mass_prod_eq_sum P Q (fun a' b' => (a', g a' b') = (a, b))]
  rw [Finsupp.sum_eq_single a]
  · by_cases ha : a ∈ P.support
    · congr 1
      conv_rhs => rw [← hg a ha, Distribution.fTransform_apply_eq_mass]
      congr 1
      funext b'
      simp
    · rw [Finsupp.notMem_support_iff.mp ha, zero_mul, zero_mul]
  · intro a' _ ha'
    rw [show (fun b' => (a', g a' b') = (a, b)) = fun _ => False from
      funext fun b' => by simp [ha']]
    simp [Distribution.mass]
  · intro _
    simp

/-- **A fiberwise pushforward** of an independent pair: moving the second sample along a map
that depends on the first, and keeps the law of the second for every possible first, keeps the
law of the pair. -/
lemma Distribution.fTransform_prod_fiber {A B : Type} (P : Distribution A)
    (Q : Distribution B) (g : A → B → B)
    (hg : ∀ a ∈ P.support, Distribution.fTransform (g a) Q = Q) :
    Distribution.fTransform (fun p => (p.1, g p.1 p.2)) (Distribution.prod P Q) =
      Distribution.prod P Q :=
  Distribution.fTransform_prod_fiber_map P Q Q g hg

/-- **Independent samples mapped coordinatewise** are independent samples of the images. -/
lemma Distribution.fTransform_pi_map {ι A B : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    [DecidableEq B] (μ : ι → Distribution A) (f : ι → A → B) :
    Distribution.fTransform (fun t i => f i (t i)) (Distribution.pi μ) =
      Distribution.pi fun i => Distribution.fTransform (f i) (μ i) := by
  classical
  ext z
  rw [Distribution.fTransform_apply_eq_mass, Distribution.mass_eq_sum, Distribution.pi_apply]
  simp only [Distribution.fTransform_apply_eq_mass, Distribution.mass_eq_sum]
  rw [Finset.prod_univ_sum]
  refine Fintype.sum_congr _ _ fun t => ?_
  rw [Distribution.pi_apply]
  by_cases h : ∀ i, f i (t i) = z i
  · rw [if_pos (funext h)]
    exact (Finset.prod_congr rfl fun i _ => if_pos (h i)).symm
  · rw [if_neg fun he => h fun i => congrFun he i]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm

/-- The mass of a fiberwise pushforward of an independent pair at a pair. -/
lemma Distribution.fTransform_prod_fiber_apply {A B B' : Type} (P : Distribution A)
    (Q : Distribution B) (g : A → B → B') (a : A) (b : B') :
    Distribution.fTransform (fun p => (p.1, g p.1 p.2)) (Distribution.prod P Q) (a, b) =
      P a * Distribution.fTransform (g a) Q b := by
  classical
  rw [Distribution.fTransform_apply_eq_mass,
    Distribution.mass_prod_eq_sum P Q (fun a' b' => (a', g a' b') = (a, b))]
  rw [Finsupp.sum_eq_single a]
  · rw [Distribution.fTransform_apply_eq_mass]
    congr 1
    congr 1
    funext b'
    simp
  · intro a' _ ha'
    rw [show (fun b' => (a', g a' b') = (a, b)) = fun _ => False from
      funext fun b' => by simp [ha']]
    simp [Distribution.mass]
  · intro ha
    simp

/-- **A map of a set into itself, injective on it, keeps the uniform law on it.** -/
lemma Distribution.fTransform_val_uniform {A : Type*} {p : A → Prop} [Fintype {a // p a}]
    [Nonempty {a // p a}] (f : A → A) (hf : ∀ a, p a → p (f a))
    (hinj : ∀ a b, p a → p b → f a = f b → a = b) :
    Distribution.fTransform f (Distribution.fTransform Subtype.val
        (Distribution.uniform {a // p a})) =
      Distribution.fTransform Subtype.val (Distribution.uniform {a // p a}) := by
  classical
  let f' : {a // p a} → {a // p a} := fun a => ⟨f a.1, hf a.1 a.2⟩
  have hinj' : Function.Injective f' := fun a b h =>
    Subtype.ext (hinj a.1 b.1 a.2 b.2 (congrArg Subtype.val h))
  let e := Equiv.ofBijective f' (Finite.injective_iff_bijective.mp hinj')
  rw [Distribution.fTransform_comp, show (f ∘ Subtype.val) = Subtype.val ∘ e from rfl,
    ← Distribution.fTransform_comp, Distribution.fTransform_equiv_uniform e]

/-- The uniform law on a set, as a law on the ambient type. -/
lemma Distribution.fTransform_val_uniform_apply {A : Type*} {p : A → Prop}
    [Fintype {a // p a}] [Nonempty {a // p a}] (y : A) [Decidable (p y)] :
    Distribution.fTransform Subtype.val (Distribution.uniform {a // p a}) y =
      if p y then 1 / (Fintype.card {a // p a} : ℝ) else 0 := by
  split_ifs with h
  · rw [show y = Subtype.val (⟨y, h⟩ : {a // p a}) from rfl,
      Distribution.fTransform_injective_apply _ _ Subtype.val_injective, Distribution.uniform_apply]
  · exact Distribution.fTransform_apply_of_forall_ne _ _ _ fun a ha => h (ha ▸ a.2)

/-- A probability distribution on a finite type sums to one. -/
lemma Distribution.sum_eq_one {A : Type*} [Fintype A] (X : Distribution A) (hX : X.isProbDist) :
    ∑ a, X a = 1 := by
  rw [← Distribution.weight_eq_sum]; exact hX.2

/-- **Updating a uniform function at a point with a uniform value** gives a uniform function. -/
lemma Distribution.fTransform_update_uniform {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq A] [Nonempty A] (i : ι) :
    Distribution.fTransform (fun p : (ι → A) × A => Function.update p.1 i p.2)
        (Distribution.uniform ((ι → A) × A)) =
      Distribution.uniform (ι → A) := by
  classical
  refine Distribution.fTransform_uniform_eq_uniform_of_card_fiber_mul _ fun T' => ?_
  -- The functions updated into `T'` are `T'` with any value at `i`.
  have fiber : (Finset.univ.filter fun p : (ι → A) × A => Function.update p.1 i p.2 = T') =
      Finset.univ.image (fun a => (Function.update T' i a, T' i)) := by
    ext ⟨T, K⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro rfl
      exact ⟨T i, by simp, by simp⟩
    · rintro ⟨a, rfl, rfl⟩
      simp
  rw [fiber, Finset.card_image_of_injective _ fun a b h => by
      simpa using congrArg (fun p : (ι → A) × A => p.1 i) h,
    Finset.card_univ, Fintype.card_prod, mul_comm]

/-- `s(cs-1) ≤ q(cq-1)` for natural numbers `s ≤ q` and `c ≥ 1`. -/
lemma natCast_mul_sub_one_le {s q : ℕ} (h : s ≤ q) {c : ℝ} (hc : 1 ≤ c) :
    (s : ℝ) * (c * s - 1) ≤ q * (c * q - 1) := by
  have hs : (s : ℝ) ≤ q := by exact_mod_cast h
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have : (1 : ℝ) ≤ c * q := by nlinarith
      simp only [Nat.cast_zero, zero_mul]
      exact mul_nonneg (by positivity) (by linarith)
  · have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hpos
    have : 0 ≤ ((q : ℝ) - s) * (c * (q + s) - 1) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith

end Probability
