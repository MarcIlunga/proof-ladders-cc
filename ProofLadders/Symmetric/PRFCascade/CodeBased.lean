import ProofLadders.Symmetric.PRFCascade.Basic
import ProofLadders.Common.Symmetric
import ProofLadders.Common.Functional
import ProofLadders.Common.LazySampling
import ConstructiveCryptography.DSL
import ConstructiveCryptography.Tactics.Substitution

/-!
# PRF cascade: the code-based proof

The notes' proof of the cascade [1, §2], replayed exactly: each hybrid is a system, each
calling program a DSL converter, and each step an equality of systems or a substitution. Two
3-hop maneuvers swap `F(K₁, ·)` and then `F(K₂, ·)` for the lazy random dictionaries `L₁` and
`L₂`, through the calling programs `𝓡₁` and `𝓡₂`, by the PRF security of `F`. With `L₁`
eliminated, a new input `X` gets `L*[X] := L₂[Y]` for a fresh uniform `Y`. A third 3-hop
maneuver, through the calling program `𝓡₃` that draws `Y` from `bday.samp()`, swaps `samp-rand`
for `samp-uniq` by the birthday lemma, within `q(q-1)/(2|X|)`; with distinct `Y`s every `L₂[Y]`
is fresh, and the hybrid is `prf-rand^H`. At `K = X = Bits λ` the bound is `q(q-1)/2^{λ+1}`.

The hybrids, in the order of the proof:

```
  prf-real^H            K₁ ‖ K₂ ← K²;  prf(X): return F(K₂, F(K₁, X))
  = 𝓡₁ • prf-real^F     K₁, K₂ separate                                  (first 3-hop maneuver)
  ≃ 𝓡₁ • prf-rand^F     F(K₁, ·) swapped for the lazy dictionary L₁      PRF security of F
  = 𝓡₂ • prf-real^F     F(K₂, ·) factored out                            (second 3-hop maneuver)
  ≃ 𝓡₂ • prf-rand^F     F(K₂, ·) swapped for the lazy dictionary L₂      PRF security of F
  = T₂ ∘ T₁             L₁ and L₂ inlined, both lazy random dictionaries
  = 𝓡₃ • samp-rand      L₁ eliminated: Y ← bday.samp() per new X         (birthday maneuver)
  ≈ 𝓡₃ • samp-uniq      samp-rand swapped for samp-uniq                  birthday lemma
  = prf-rand^H          distinct Y: L₂[Y] always fresh
```

In the sampled-function form of the libraries a lazy random dictionary is a function sampled
once, `prf-rand^F` is the uniform random function `URF` (`Common/Symmetric`), and the dictionary
`L₁` of `𝓡₂` is its initial sample `T₁`. The notes' cache `L*` of past answers changes nothing on
a function; it enters with the calling program `𝓡₃`, the notes' last hybrid with the lazy
dictionaries `L*` and `L₂`.

## Main definitions

* `𝓡₁ F`, `𝓡₂ X`, `𝓡₃ X`: the calling programs of the two swaps and of the birthday maneuver
* `keysL₂ ys r`, `valueLstar law tZ ys r`: the keys of `L₂` and the values of `L*` in `𝓡₃`

## Main results

* `𝓡₁_smul_prfReal`, `𝓡₁_smul_urf`, `𝓡₂_smul_urf`: the equalities around the two swaps
* `𝓡₃_smul_prgRand`, `𝓡₃_smul_sampUniq`: the calling program of the birthday maneuver on
  `samp-rand` and on `samp-uniq`
* `birthday_maneuver`: the birthday maneuver, within `q(q-1)/(2|X|)`
* `prf_cascade`, `prf_cascade_bits`: the cascade is a secure PRF

## References

1. The symmetric proof ladder, *Security proofs in the style of The Joy of Cryptography*,
   `proof-ladders/symmetric-ladder`, `Notes/selfcontained.tex`.
-/

namespace ProofLadders.PRFCascade.CodeBased

open Commons Probability SystemAlgebra SystemAlgebra.DSL SystemAlgebra.Interface
open scoped SystemAlgebra SystemAlgebra.DSL

/-! ### The calling programs -/

section

variable {K X : Type} [Fintype K] [Nonempty K] [Fintype X]

-- `𝓡₁`: `K₂ ← K`; on `X`, `Y ← prf.query(X)` and return `F(K₂, Y)`.
converter 𝓡₁(F : K → X → X) : Evaluation X X
  inside prf : Evaluation X X
  initialize
    k₂ ←$ 𝒰[K]
  on eval(x : X) → X
    y ← prf.eval(x)
    return F k₂ y

end

-- `𝓡₂`: the lazy random dictionary `L₁`, sampled once as `T₁`; on `X`, return
-- `prf.query(L₁[X])`.
converter 𝓡₂(X : Type) [Fintype X] [DecidableEq X] [Nonempty X] : Evaluation X X
  inside prf : Evaluation X X
  initialize
    T₁ ←$ 𝒰[X → X]
  on eval(x : X) → X
    z ← prf.eval(T₁ x)
    return z

-- `𝓡₃`, the notes' last hybrid: on a new `X`, `Y ← bday.samp()`; if `L₂[Y]` is undefined,
-- `L₂[Y] ← 𝒰[X]`; `L*[X] := L₂[Y]`; return `L*[X]`. (`L*` is `Lstar`.)
converter 𝓡₃(X : Type) [Fintype X] [DecidableEq X] [Nonempty X] : Evaluation X X
  inside bday : Evaluation Unit X
  initialize
    Lstar ← ([] : List (X × X))
    L₂ ← ([] : List (X × X))
  on eval(x : X) → X
    match Lstar.lookup x
    | some z →
      return z
    | none →
      Y ← bday.eval(())
      match L₂.lookup Y
      | some z →
        Lstar ← Lstar ++ [(x, z)]
        return z
      | none →
        z ←$ 𝒰[X]
        L₂ ← L₂ ++ [(Y, z)]
        Lstar ← Lstar ++ [(x, z)]
        return z

/-! ### The two swaps

`𝓡₁` samples `K₂` once and `𝓡₂` the dictionary `T₁` once, each then calling per query, so on a
function they are sampled functions: on `prf-real^F` the first swap gives `prf-real^H`, then
`𝓡₂ • prf-real^F`, and on the uniform random function `T₂ ∘ T₁`. -/

noncomputable section

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {K : Type} [Fintype K] [Nonempty K]

omit [DecidableEq X] [Nonempty X] in
/-- `𝓡₁` against `g` and a source table: the first invocation reads `K₂` from the table. -/
lemma 𝓡₁_combine_first (F : K → X → X) (g : X → X) {k : ℕ} (t : Fin k → K) (c : ℕ)
    (x : X) :
    (𝓡₁.body F).combine (parallelStep (fun (_ : Unit) _ x => ((), g x))
        (sourceStep (q := k) (𝓡₁.law1 F))) (𝓡₁.bound_spec F)
        (none, ((), (t, c))) .eval x =
      ((some (sourceEntry (𝓡₁.law1 F) t c), ((), (t, c + 1))),
        F (sourceEntry (𝓡₁.law1 F) t c) (g x)) :=
  -- Two inside calls: `randomness ⇒ K₂` (the `c`-th entry), then `prf(x)`, answered `g x`.
  Program.combine_eq_of_invoke _ _ (n := 2) (by
    simp [Program.invoke, 𝓡₁.body, callProg, returnProg, parallelStep, sourceStep, sourceEntry])

omit [DecidableEq X] [Nonempty X] in
/-- `𝓡₁` against `g` once `K₂` is stored. -/
lemma 𝓡₁_combine_later (F : K → X → X) (g : X → X) {k : ℕ} (k₂ : K)
    (r : Unit × ((Fin k → K) × ℕ)) (x : X) :
    (𝓡₁.body F).combine (parallelStep (fun (_ : Unit) _ x => ((), g x))
        (sourceStep (q := k) (𝓡₁.law1 F))) (𝓡₁.bound_spec F)
        (some k₂, r) .eval x = ((some k₂, r), F k₂ (g x)) :=
  -- One inside call: `prf(x)`, answered `g x`; the stored `K₂` is used.
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, 𝓡₁.body, callProg, returnProg, parallelStep])

/-- `𝓡₂` against `g` and a source table: the first invocation reads `T₁` from the table. -/
lemma 𝓡₂_combine_first (g : X → X) {k : ℕ} (t : Fin k → (X → X)) (c : ℕ) (x : X) :
    (𝓡₂.body X).combine (parallelStep (fun (_ : Unit) _ x => ((), g x))
        (sourceStep (q := k) (𝓡₂.law1 X))) (𝓡₂.bound_spec X)
        (none, ((), (t, c))) .eval x =
      ((some (sourceEntry (𝓡₂.law1 X) t c), ((), (t, c + 1))),
        g (sourceEntry (𝓡₂.law1 X) t c x)) :=
  -- Two inside calls: `randomness ⇒ T₁` (the `c`-th entry), then `prf(T₁ x)`, answered
  -- `g (T₁ x)`.
  Program.combine_eq_of_invoke _ _ (n := 2) (by
    simp [Program.invoke, 𝓡₂.body, callProg, returnProg, parallelStep, sourceStep, sourceEntry])

/-- `𝓡₂` against `g` once `T₁` is stored. -/
lemma 𝓡₂_combine_later (g : X → X) {k : ℕ} (T₁ : X → X) (r : Unit × ((Fin k → (X → X)) × ℕ))
    (x : X) :
    (𝓡₂.body X).combine (parallelStep (fun (_ : Unit) _ x => ((), g x))
        (sourceStep (q := k) (𝓡₂.law1 X))) (𝓡₂.bound_spec X)
        (some T₁, r) .eval x = ((some T₁, r), g (T₁ x)) :=
  -- One inside call: `prf(T₁ x)`, answered `g (T₁ x)`; the stored `T₁` is used.
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, 𝓡₂.body, callProg, returnProg, parallelStep])

omit [DecidableEq X] [Nonempty X] in
/-- **`𝓡₁` on a function** `g`: a uniform `K₂`, then `F(K₂, g(x))`. -/
lemma 𝓡₁_smul_ofFunction (F : K → X → X) (q : Evaluation.Port → ℕ) (g : X → X) :
    𝓡₁.perPort F (budget := q) • Resource.ofFunction (fun _ => g) =
      Resource.sample (Distribution.uniform K) fun k₂ =>
        Resource.ofFunction (A := Queries X q) fun _ x => F k₂ (g x) := by
  -- `𝓡₁` is its program with its source of keys beside the inside interface.
  rw [𝓡₁.perPort, 𝓡₁.randomness, 𝓡₁.perPortProgram]
  -- The initialization sample is the converter's only randomness: the source is read once, at
  -- the first invocation, and from then on `𝓡₁` against `g` is the function `F(K₂, g(·))`.
  refine Converter.ofPreservingProgram_source_smul_ofFunction (A := Queries X q)
    (B := Queries X q) (Z := K) (k := 𝓡₁.bound F * ∑ i, q i) none
    (𝓡₁.body F) (𝓡₁.bound_spec F) (𝓡₁.portMap F) _ q _ _
    (𝓡₁.law1 F) (fun _ => g) (fun k₂ _ x => F k₂ (g x))
    (fun t c => automatonSystem_of_stored _ (fun k₂ _ x => F k₂ (g x)) ((), (t, c))
      (sourceEntry (𝓡₁.law1 F) t c)
      (fun j x => ⟨_, 𝓡₁_combine_first F g t c x⟩)
      (fun r j x => ⟨_, 𝓡₁_combine_later F g _ r x⟩))
    -- (The source has an entry whenever a history is admitted.)
    fun _ hd => Nat.mul_pos (by norm_num [𝓡₁.bound]) (bound_pos_of_domain hd)

/-- **`𝓡₂` on a function** `g`: a uniform dictionary `T₁`, then `g(T₁(x))`. -/
lemma 𝓡₂_smul_ofFunction (q : Evaluation.Port → ℕ) (g : X → X) :
    𝓡₂.perPort X (budget := q) • Resource.ofFunction (fun _ => g) =
      Resource.sample (Distribution.uniform (X → X)) fun T₁ =>
        Resource.ofFunction (A := Queries X q) fun _ x => g (T₁ x) := by
  -- `𝓡₂` is its program with its source of dictionaries beside the inside interface.
  rw [𝓡₂.perPort, 𝓡₂.randomness, 𝓡₂.perPortProgram]
  -- As `𝓡₁_smul_ofFunction`, with `T₁` the initialization sample: against `g`, `𝓡₂` is the
  -- function `g(T₁(·))`.
  refine Converter.ofPreservingProgram_source_smul_ofFunction (A := Queries X q)
    (B := Queries X q) (Z := X → X) (k := 𝓡₂.bound X * ∑ i, q i)
    none (𝓡₂.body X) (𝓡₂.bound_spec X) (𝓡₂.portMap X) _ q _ _
    (𝓡₂.law1 X) (fun _ => g) (fun T₁ _ x => g (T₁ x))
    (fun t c => automatonSystem_of_stored _ (fun T₁ _ x => g (T₁ x)) ((), (t, c))
      (sourceEntry (𝓡₂.law1 X) t c)
      (fun j x => ⟨_, 𝓡₂_combine_first g t c x⟩)
      (fun r j x => ⟨_, 𝓡₂_combine_later g _ r x⟩))
    -- (The source has an entry whenever a history is admitted.)
    fun _ hd => Nat.mul_pos (by norm_num [𝓡₂.bound]) (bound_pos_of_domain hd)

omit [DecidableEq X] [Nonempty X] in
/-- **The first hop**, "separate `K₁` from `K₂`": `𝓡₁` on `prf-real^F` is `prf-real^H`. -/
lemma 𝓡₁_smul_prfReal (F : K → X → X) (q : Evaluation.Port → ℕ) :
    𝓡₁.perPort F (budget := q) • PRF.Real F = PRF.Real (H F) := by
  --   D ─ 𝓡₁ ─ prf-real^F:   K₁ ← K;  K₂ ← K in 𝓡₁;  eval(x) ⇒ F(K₂, F(K₁, x))
  --   D ─ prf-real^H:        (K₁, K₂) ← K²;           eval(x) ⇒ F(K₂, F(K₁, x))
  -- `prf-real^F` samples a key `K₁` and is the function `F(K₁, ·)`.
  unfold PRF.Real
  -- On the function `F(K₁, ·)`, `𝓡₁` samples `K₂` and is `F(K₂, F(K₁, ·))`.
  have h₁ : ∀ k, 𝓡₁.perPort F (budget := q) • Resource.ofFunction (fun _ x => F k x) =
      Resource.sample (Distribution.uniform K) fun k₂ =>
        Resource.ofFunction (A := Queries X q) fun _ x => F k₂ (F k x) :=
    fun k => 𝓡₁_smul_ofFunction F q (F k)
  -- Attaching `𝓡₁` to the sampled `K₁` attaches it to each sample, ...
  rw [Resource.smul_sample]
  simp only [h₁]
  -- ... and sampling `K₁` and then `K₂` is sampling the pair ...
  rw [Resource.sample_sample]
  congr 1
  -- ... whose law is the uniform law on `K × K`.
  exact Distribution.prod_uniform

/-- **The middle hop**, "inline `L₁`, factor out `F(K₂, ·)`": `𝓡₁` on the uniform random
function is `𝓡₂` on `prf-real^F`, both `F(K₂, T₁(x))` for a uniform `K₂` and a uniform `T₁`. -/
lemma 𝓡₁_smul_urf (F : K → X → X) (q : Evaluation.Port → ℕ) :
    𝓡₁.perPort F (budget := q) • URF (Queries X q) = 𝓡₂.perPort X • PRF.Real F := by
  --   D ─ 𝓡₁ ─ prf-rand^F:   T₁ ← URF;  K₂ ← K in 𝓡₁;  eval(x) ⇒ F(K₂, T₁(x))
  --   D ─ 𝓡₂ ─ prf-real^F:   K₂ ← K;  T₁ ← (X → X) in 𝓡₂;  eval(x) ⇒ F(K₂, T₁(x))
  -- `prf-real^F` samples a key `K₂` and is the function `F(K₂, ·)`.
  unfold PRF.Real
  -- On the function `F(K₂, ·)`, `𝓡₂` samples `T₁` and is `F(K₂, T₁(·))`.
  have h₂ : ∀ k, 𝓡₂.perPort X (budget := q) • Resource.ofFunction (fun _ x => F k x) =
      Resource.sample (Distribution.uniform (X → X)) fun T₁ =>
        Resource.ofFunction (A := Queries X q) fun _ x => F k (T₁ x) :=
    fun k => 𝓡₂_smul_ofFunction q (F k)
  -- The uniform random function samples a function once (`URF_perPort_eq`); attaching each
  -- converter to a sample attaches it to each sampled function.
  rw [URF_perPort_eq, Resource.smul_sample, Resource.smul_sample]
  simp only [𝓡₁_smul_ofFunction, h₂]
  -- Both are `F(K₂, T₁(·))`, with `T₁` and `K₂` sampled independently, in either order.
  exact Resource.sample_comm _ _ _

variable (X) in
/-- **The hop after the second swap**, "inline `L₂`": `𝓡₂` on the uniform random function is
`T₂ ∘ T₁`, the two lazy random dictionaries as uniform functions. -/
lemma 𝓡₂_smul_urf (q : Evaluation.Port → ℕ) :
    𝓡₂.perPort X (budget := q) • URF (Queries X q) = composedURF X := by
  --   D ─ 𝓡₂ ─ prf-rand^F:   T₂ ← URF;  T₁ ← (X → X) in 𝓡₂;  eval(x) ⇒ T₂(T₁(x))
  -- The uniform random function samples `T₂` once; `𝓡₂` attaches to each sample, ...
  rw [URF_perPort_eq, Resource.smul_sample]
  -- ... where it samples `T₁` and is `T₂(T₁(·))`.
  simp only [𝓡₂_smul_ofFunction]
  -- Sampling `T₂` then `T₁` is sampling `T₁` then `T₂`, which is sampling the pair ...
  rw [Resource.sample_comm, Resource.sample_sample]
  unfold composedURF
  congr 1
  -- ... whose law is the uniform law on pairs of functions.
  exact Distribution.prod_uniform

end

/-! ### The birthday maneuver

The notes' last hybrid is the calling program `𝓡₃` on `samp-rand`; there `Y` is uniform, so two
inputs can get the same `Y` and share `L₂[Y]`. On `samp-uniq` the `Y`s are distinct, so every
`L₂[Y]` is fresh. To compare `𝓡₃` with the sampled functions, we run it on tables: the library
behind `bday` answers its calls `ys 0, ys 1, …` in order, and the fresh values of `L₂` are the
entries `tZ 0, tZ 1, …` of `𝓡₃`'s own table of samples. Then `𝓡₃` answers the query of rank `r`
(the `r`-th distinct input) with `L₂[ys r]`: the entry of `tZ` at the rank of `ys r` among the
keys of `L₂`, in the order of their first occurrences. That is the lazy random dictionary
(`Common/LazySampling`) on the table of these values. -/

section Keys

variable {X : Type} [DecidableEq X]

/-- **The keys of `L₂`** after `r` calls to `bday`: the answers `ys 0, …, ys (r-1)`, in the order
of their first occurrences. -/
def keysL₂ (ys : ℕ → X) (r : ℕ) : List X :=
  List.firstOccurrences ((List.range r).map ys)

/-- One more call to `bday` adds its answer to the keys of `L₂` if it is new. -/
lemma keysL₂_succ (ys : ℕ → X) (r : ℕ) :
    keysL₂ ys (r + 1) = if ys r ∈ keysL₂ ys r then keysL₂ ys r else keysL₂ ys r ++ [ys r] := by
  -- The answers up to `r` are those up to `r - 1`, then `ys r`; first occurrences of a list
  -- extended by one element.
  rw [keysL₂, List.range_succ, List.map_append, List.map_singleton,
    List.firstOccurrences_append_singleton]
  rfl

/-- **The value `L*[X]`** of the query of rank `r`: `L₂[Y]` for its answer `Y = ys r`, the entry
of the table `tZ` of `L₂` at the rank of `Y` among the keys of `L₂`. -/
noncomputable def valueLstar {m : ℕ} (law : Distribution.ProbDist X) (tZ : Fin m → X)
    (ys : ℕ → X) (r : ℕ) : X :=
  sourceEntry law tZ ((keysL₂ ys (r + 1)).idxOf (ys r))

/-- **With distinct answers**, the keys of `L₂` are all the answers so far. -/
lemma keysL₂_of_injective (ys : ℕ → X) {r : ℕ}
    (distinct : ∀ i < r, ∀ j < r, ys i = ys j → i = j) :
    keysL₂ ys r = (List.range r).map ys := by
  -- Induction on the number `r` of calls.
  induction r with
  | zero => rfl
  | succ r ih =>
    -- The new answer `ys r` is none of the earlier ones: `ys i = ys r` with `i < r` would make
    -- `i = r` by distinctness, ...
    have fresh : ys r ∉ (List.range r).map ys := by
      intro hr
      obtain ⟨i, hi, he⟩ := List.mem_map.mp hr
      have := distinct i (by simp at hi; omega) r (by omega) he
      simp at hi; omega
    -- ... so it is appended to the keys, which are the earlier answers.
    rw [keysL₂_succ, ih (fun i hi j hj => distinct i (by omega) j (by omega)), if_neg fresh,
      List.range_succ, List.map_append, List.map_singleton]

/-- **With distinct answers, `L₂[Y]` is always fresh**: the query of rank `r` gets the entry `r`
of the table of `L₂`. -/
lemma valueLstar_of_injective {m : ℕ} (law : Distribution.ProbDist X) (tZ : Fin m → X)
    (ys : ℕ → X) {r : ℕ} (distinct : ∀ i ≤ r, ∀ j ≤ r, ys i = ys j → i = j) :
    valueLstar law tZ ys r = sourceEntry law tZ r := by
  -- The answer `ys r` is none of the earlier ones: `ys i = ys r` with `i < r` would make `i = r`
  -- by distinctness.
  have fresh : ys r ∉ (List.range r).map ys := by
    intro hr
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hr
    have := distinct i (by simp at hi; omega) r le_rfl he
    simp at hi; omega
  -- The keys of `L₂` after `r + 1` calls are the `r` earlier answers, then `ys r`, ...
  rw [valueLstar, keysL₂_of_injective ys (fun i hi j hj => distinct i (by omega) j (by omega)),
    List.range_succ, List.map_append, List.map_singleton, List.idxOf_append_of_notMem fresh]
  -- ... where `ys r` has rank `r`.
  simp

end Keys

noncomputable section

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]

/-! The three branches of `𝓡₃`, against an inside step `g` (the library behind `bday`) and
`𝓡₃`'s own table `tZ` of samples, read at the position `cZ`. `𝓡₃` holds `(L*, L₂)`; before its
first invocation it holds nothing, and both dictionaries are empty. -/

/-- `𝓡₃` when `L*[X]` is defined: it returns `L*[X]`, without inside calls. -/
lemma 𝓡₃.combine_cached {R : Type} (g : R → (j : (Evaluation Unit X 0).I) →
      (Evaluation Unit X 0).X j → R × (Evaluation Unit X 0).Y j) {m : ℕ}
    {stored : Option (List (X × X) × List (X × X))} {Lstar L₂ : List (X × X)}
    (hs : stored.getD ([], []) = (Lstar, L₂)) (r : R) (tZ : Fin m → X) (cZ : ℕ) {x z : X}
    (hx : Lstar.lookup x = some z) :
    (𝓡₃.body X).combine (parallelStep g (sourceStep (q := m) (𝓡₃.law1 X))) (𝓡₃.bound_spec X)
        (stored, (r, (tZ, cZ))) .eval x = ((some (Lstar, L₂), (r, (tZ, cZ))), z) :=
  -- No inside call: the body looks up `L*[x]` and returns it. (Before the first invocation
  -- `L*` is empty, and no `L*[x]` is defined.)
  Program.combine_eq_of_invoke _ _ (n := 0) (by
    cases stored <;> simp only [Option.getD, Prod.mk.injEq] at hs <;>
      obtain ⟨rfl, rfl⟩ := hs <;> simp_all [Program.invoke, 𝓡₃.body, returnProg])

/-- `𝓡₃` when `L*[X]` is undefined and `L₂[Y]` is defined for the answer `Y` of `bday`: it
records `L*[X] := L₂[Y]` and returns it. -/
lemma 𝓡₃.combine_stored {R : Type} (g : R → (j : (Evaluation Unit X 0).I) →
      (Evaluation Unit X 0).X j → R × (Evaluation Unit X 0).Y j) {m : ℕ}
    {stored : Option (List (X × X) × List (X × X))} {Lstar L₂ : List (X × X)}
    (hs : stored.getD ([], []) = (Lstar, L₂)) (r : R) (tZ : Fin m → X) (cZ : ℕ) {x z : X}
    (hx : Lstar.lookup x = none) (hy : L₂.lookup (g r .eval ()).2 = some z) :
    (𝓡₃.body X).combine (parallelStep g (sourceStep (q := m) (𝓡₃.law1 X))) (𝓡₃.bound_spec X)
        (stored, (r, (tZ, cZ))) .eval x =
      ((some (Lstar ++ [(x, z)], L₂), ((g r .eval ()).1, (tZ, cZ))), z) :=
  -- One inside call, `bday.eval(()) ⇒ Y`; `L₂[Y] = z` is defined. (Before the first invocation
  -- `L₂` is empty, so this branch does not occur.)
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    cases stored <;> simp only [Option.getD, Prod.mk.injEq] at hs <;> obtain ⟨rfl, rfl⟩ := hs
    · simp at hy
    · simp [Program.invoke, 𝓡₃.body, callProg, returnProg, parallelStep, hx, hy])

/-- `𝓡₃` when `L*[X]` and `L₂[Y]` are undefined: it samples `L₂[Y]`, the entry `cZ` of its table,
records `L*[X] := L₂[Y]` and returns it. -/
lemma 𝓡₃.combine_fresh {R : Type} (g : R → (j : (Evaluation Unit X 0).I) →
      (Evaluation Unit X 0).X j → R × (Evaluation Unit X 0).Y j) {m : ℕ}
    {stored : Option (List (X × X) × List (X × X))} {Lstar L₂ : List (X × X)}
    (hs : stored.getD ([], []) = (Lstar, L₂)) (r : R) (tZ : Fin m → X) (cZ : ℕ) {x : X}
    (hx : Lstar.lookup x = none) (hy : L₂.lookup (g r .eval ()).2 = none) :
    (𝓡₃.body X).combine (parallelStep g (sourceStep (q := m) (𝓡₃.law1 X))) (𝓡₃.bound_spec X)
        (stored, (r, (tZ, cZ))) .eval x =
      ((some (Lstar ++ [(x, sourceEntry (𝓡₃.law1 X) tZ cZ)],
          L₂ ++ [((g r .eval ()).2, sourceEntry (𝓡₃.law1 X) tZ cZ)]),
        ((g r .eval ()).1, (tZ, cZ + 1))), sourceEntry (𝓡₃.law1 X) tZ cZ) :=
  -- Two inside calls: `bday.eval(()) ⇒ Y`, then `randomness ⇒ z` (the `cZ`-th entry).
  Program.combine_eq_of_invoke _ _ (n := 2) (by
    cases stored <;> simp only [Option.getD, Prod.mk.injEq] at hs <;> obtain ⟨rfl, rfl⟩ := hs <;>
      simp [Program.invoke, 𝓡₃.body, callProg, returnProg, parallelStep, sourceStep, sourceEntry,
        hx, hy] <;> rfl)

variable (X) in
/-- **`𝓡₃` on tables is a lazy random dictionary**: against a library answering its calls
`ys 0, ys 1, …` in order, and with its own table `tZ`, `𝓡₃` is the lazy random dictionary on the
inputs whose value at rank `r` is `L*[X] = L₂[ys r]` (`valueLstar`). -/
lemma 𝓡₃_combine_eq_lazyDictionary {R : Type} (g : R → (j : (Evaluation Unit X 0).I) →
      (Evaluation Unit X 0).X j → R × (Evaluation Unit X 0).Y j) {m : ℕ}
    (q : Evaluation.Port → ℕ) (stB : ℕ → R) (ys : ℕ → X)
    (hB : ∀ c, g (stB c) .eval () = (stB (c + 1), ys c)) (tZ : Fin m → X) :
    Resource.ofAutomaton (Queries X q)
        ((𝓡₃.body X).combine (parallelStep g (sourceStep (𝓡₃.law1 X))) (𝓡₃.bound_spec X))
        (Distribution.ProbDist.single (none, (stB 0, (tZ, 0)))) =
      Resource.ofAutomaton (Queries X q)
        (lazyDictionary (Queries X q) (𝓡₃.law1 X)
          (fun r : Fin (q .eval) => valueLstar (𝓡₃.law1 X) tZ ys r) (fun _ x => x)
          (fun _ _ z => z))
        (Distribution.ProbDist.single []) := by
  --   eval(x) ──► 𝓡₃ (L*, L₂) ── bday.eval(()) ──► library ⇒ ys 0, ys 1, …
  --                           ── randomness   ──► table tZ ⇒ tZ 0, tZ 1, …
  --
  -- The two automata agree along the domain, with the dictionary `D` (the inputs so far, in
  -- the order of their first queries) related to the state of `𝓡₃` by: `bday` and the table
  -- are at positions `|D|` and `|keys of L₂|`; `L*` holds the values of `D`; `L₂` holds the
  -- entries of `tZ` at the ranks of its keys; and `D` has at most as many inputs as the history.
  refine Resource.ofAutomaton_single_congr_on_domain (fun h st D =>
    st.2 = (stB D.length, (tZ, (keysL₂ ys D.length).length)) ∧
    (∀ x, (st.1.getD ([], [])).1.lookup x =
      if x ∈ D then some (valueLstar (𝓡₃.law1 X) tZ ys (D.idxOf x)) else none) ∧
    (∀ y, (st.1.getD ([], [])).2.lookup y =
      if y ∈ keysL₂ ys D.length then
        some (sourceEntry (𝓡₃.law1 X) tZ ((keysL₂ ys D.length).idxOf y)) else none) ∧
    D.length ≤ h.length) ⟨by simp [keysL₂], by simp, by simp [keysL₂], le_rfl⟩ ?_
  -- One query `x`, admitted after the history `h`, from related states.
  rintro h ⟨⟨⟩, x⟩ ⟨stored, rB, tZ', cZ⟩ D hd ⟨hst, hL, hL₂, hlen⟩
  -- The library and the table are at the positions the relation gives.
  obtain ⟨rfl, rfl, rfl⟩ : rB = stB D.length ∧ tZ' = tZ ∧ cZ = (keysL₂ ys D.length).length := by
    simpa using hst
  -- The two dictionaries of `𝓡₃`.
  rcases hs : stored.getD ([], []) with ⟨Lstar, L₂⟩
  rw [hs] at hL hL₂
  dsimp only at hL hL₂
  -- The history has fewer than `q` queries, so the ranks are below `q`.
  have hq : h.length < q .eval := by
    simpa using evaluation_length_le (q := q) (Or.inr hd)
  by_cases hx : x ∈ D
  · -- `x` was queried: `𝓡₃` returns `L*[x]`, its value, without inside calls, ...
    rw [𝓡₃.combine_cached g hs _ _ _ ((hL x).trans (if_pos hx))]
    -- ... and the lazy dictionary, which holds `x`, returns its table at the rank of `x`, ...
    simp only [lazyDictionary, if_pos hx]
    -- ... which is below `|D| ≤ |h| < q`.
    have hr : D.idxOf x < q .eval :=
      ((List.idxOf_lt_length_of_mem hx).trans_le hlen).trans hq
    -- Same answer; neither state changes; `D` is still no longer than the history.
    exact ⟨(sourceEntry_of_lt (𝓡₃.law1 X)
      (fun r : Fin (q .eval) => valueLstar (𝓡₃.law1 X) tZ' ys r) hr).symm, trivial, hL, hL₂,
      by simp; omega⟩
  · -- `x` is new: `L*[x]` is undefined, ...
    have hxL : Lstar.lookup x = none := (hL x).trans (if_neg hx)
    -- ... `𝓡₃` calls `bday`, which answers `ys |D|`, ...
    have hB' := hB D.length
    -- ... and `x` gets the rank `|D|`, below `q`.
    have hr : (D ++ [x]).idxOf x = D.length := by
      rw [List.idxOf_append_of_notMem hx]; simp
    have hrq : D.length < q .eval := hlen.trans_lt hq
    by_cases hy : ys D.length ∈ keysL₂ ys D.length
    · -- `Y = ys |D|` is a key of `L₂`: the keys of `L₂` do not change, ...
      have hkeys : keysL₂ ys (D.length + 1) = keysL₂ ys D.length := by
        rw [keysL₂_succ, if_pos hy]
      -- ... and `L₂[Y]` is the value of the query of rank `|D|`.
      have hyL : L₂.lookup (g (stB D.length) .eval ()).2 =
          some (valueLstar (𝓡₃.law1 X) tZ' ys D.length) := by
        rw [hB', valueLstar, hkeys]; exact (hL₂ _).trans (if_pos hy)
      -- `𝓡₃` records `L*[x] := L₂[Y]` and returns it; the lazy dictionary adds `x` to `D` and
      -- returns its table at the rank `|D|`.
      rw [𝓡₃.combine_stored g hs _ _ _ hxL hyL, hB']
      simp only [lazyDictionary, if_neg hx]
      -- Same answer; the positions; `L*` holds the values of `D ++ [x]`; `L₂` is unchanged;
      -- one more input and one more query.
      refine ⟨by rw [hr, sourceEntry_of_lt (𝓡₃.law1 X)
        (fun r : Fin (q .eval) => valueLstar (𝓡₃.law1 X) tZ' ys r) hrq], by simp [hkeys],
        fun x' => ?_, ?_, by simp; omega⟩
      · -- An association list extended by a new key holds the extended dictionary.
        exact lookup_append_of_dictionary id Function.injective_id hL hx x'
      · intro y
        simpa [hkeys] using hL₂ y
    · -- `Y = ys |D|` is a new key: it is appended to the keys of `L₂`, ...
      have hkeys : keysL₂ ys (D.length + 1) = keysL₂ ys D.length ++ [ys D.length] := by
        rw [keysL₂_succ, if_neg hy]
      -- ... `L₂[Y]` is undefined, ...
      have hyL : L₂.lookup (g (stB D.length) .eval ()).2 = none := by
        rw [hB']; exact (hL₂ _).trans (if_neg hy)
      -- ... and the next entry of the table, at the rank of `Y` among the keys of `L₂`, is the
      -- value of the query of rank `|D|`.
      have hz : sourceEntry (𝓡₃.law1 X) tZ' (keysL₂ ys D.length).length =
          valueLstar (𝓡₃.law1 X) tZ' ys D.length := by
        rw [valueLstar, hkeys, List.idxOf_append_of_notMem hy]; simp
      -- `𝓡₃` samples `L₂[Y]`, records `L*[x] := L₂[Y]` and returns it; the lazy dictionary adds
      -- `x` to `D` and returns its table at the rank `|D|`.
      rw [𝓡₃.combine_fresh g hs _ _ _ hxL hyL, hB', hz]
      simp only [lazyDictionary, if_neg hx]
      -- Same answer; the positions; `L*` holds the values of `D ++ [x]`; `L₂` holds one more
      -- key; one more input and one more query.
      refine ⟨by rw [hr, sourceEntry_of_lt (𝓡₃.law1 X)
        (fun r : Fin (q .eval) => valueLstar (𝓡₃.law1 X) tZ' ys r) hrq], by simp [hkeys],
        fun x' => ?_, fun y => ?_, by simp; omega⟩
      · -- An association list extended by a new key holds the extended dictionary.
        exact lookup_append_of_dictionary id Function.injective_id hL hx x'
      · -- The same for `L₂`, extended by `Y` with the next entry of the table.
        have new := lookup_append_of_dictionary id Function.injective_id
          (f := sourceEntry (𝓡₃.law1 X) tZ') hL₂ hy y
        rw [hz] at new
        simp only [List.length_append, List.length_singleton, hkeys]
        exact new

variable (X) in
/-- **`𝓡₃` attached to an automaton started on a sampled table** samples that table and its own
table, and runs on both. -/
lemma 𝓡₃_smul_ofAutomaton {R : Type} (g : R → (j : (Evaluation Unit X 0).I) →
      (Evaluation Unit X 0).X j → R × (Evaluation Unit X 0).Y j)
    (q : Evaluation.Port → ℕ) {ZB : Type} [Fintype ZB]
    (lawB : Distribution.ProbDist ZB) {n : ℕ} (initB : (Fin n → ZB) → R) :
    𝓡₃.perPort X (budget := q) •
        Resource.ofAutomaton (Evaluation.perPort Unit X (𝓡₃.insideBudget X q)) g
          ⟨Distribution.fTransform initB (Distribution.pi fun _ : Fin n => lawB.1),
            Distribution.fTransform_isProbDist _ (Distribution.pi_isProbDist fun _ => lawB.2)⟩ =
      Resource.sample (Distribution.prod (Distribution.pi fun _ : Fin n => lawB.1)
          (Distribution.pi fun _ : Fin (𝓡₃.bound X * ∑ i, q i) => (𝓡₃.law1 X).1))
        fun t => Resource.ofAutomaton (Queries X q)
          ((𝓡₃.body X).combine (parallelStep g (sourceStep (𝓡₃.law1 X))) (𝓡₃.bound_spec X))
          (Distribution.ProbDist.single (none, (initB t.1, (t.2, 0)))) := by
  --            ┌─────────┐ ── bday.eval(()) ──► ┌────────────────────────┐
  --   eval(x)  │ program │                      │ library, table tB      │
  --   ───────► │ of 𝓡₃   │                      └────────────────────────┘
  --   ◄─────── │ (L*,L₂) │ ── randomness(()) ─► ┌────────────────────────┐
  --            └─────────┘                      │ source of 𝓡₃, table tZ │
  --                                             └────────────────────────┘
  --
  -- `𝓡₃` is its program with its source beside the inside interface `bday`:
  --   (program ≫ rightContext source) • library = program • (library ∥ source).
  rw [𝓡₃.perPort, 𝓡₃.randomness, 𝓡₃.perPortProgram, Interface.comp_smul, attach_rightContext]
  -- The library and the source are automata on independent tables, side by side one automaton,
  -- and the program attached to it is the combined automaton.
  rw [Resource.source, parallel_ofAutomaton, Converter.ofPreservingProgram_smul_ofAutomaton]
  -- An automaton with a sampled initial state samples the automaton started there; it remains
  -- to see the initial law as the pair of tables pushed forward.
  rw [← Resource.ofAutomaton_fTransform]
  congr 1
  apply Subtype.ext
  change Distribution.fTransform _ (Distribution.prod (Distribution.fTransform _ _)
    (Distribution.fTransform _ _)) = _
  -- A product of pushforwards is the pushforward of the product; pushforwards compose.
  rw [← Distribution.fTransform_prod, Distribution.fTransform_comp]
  rfl

variable (X) in
/-- **Eliminate `L₁`** [1, §2]: `𝓡₃` on `samp-rand` is `T₂ ∘ T₁`. The `Y`s are fresh uniform
samples, one per new input, as the values of the lazy dictionary `L₁`; `L₂`, filled lazily from
`𝓡₃`'s samples, is a uniform function `T₂` on them. -/
lemma 𝓡₃_smul_prgRand (q : Evaluation.Port → ℕ) :
    𝓡₃.perPort X (budget := q) • PRG.Rand.perPort X (budget := 𝓡₃.insideBudget X q) =
      composedURF X := by
  classical
  --   D ─ 𝓡₃ (L*, L₂) ─ samp-rand:  eval(x) for a new x:  bday.eval(()) ⇒ Y, Y ← 𝒰[X];
  --                                  L₂[Y] ← 𝒰[X] if undefined;  eval ⇒ L₂[Y]
  --   D ─ T₂ ∘ T₁:                   eval(x) ⇒ T₂(T₁(x)),  (T₁, T₂) ← 𝒰[(X → X)²]
  --
  -- `samp-rand` is its program run on its table `tY` of samples.
  unfold PRG.Rand.perPort Converter.ofProgram PRG.Rand.randomness Resource.source
  rw [ofDDC_ofProgramOn_smul_ofAutomaton_pi (A := Evaluation.perPort Unit X (𝓡₃.insideBudget X q))
    (B := Interface.source X (PRG.Rand.bound X * ∑ i, 𝓡₃.insideBudget X q i))
    none (PRG.Rand.body X) (PRG.Rand.bound_spec X)]
  -- `𝓡₃` on it samples `tY` and its own table `tZ`.
  rw [𝓡₃_smul_ofAutomaton]
  -- The answers of `samp-rand`: the entries of `tY`, in order.
  let ys : (Fin (PRG.Rand.bound X * ∑ i, 𝓡₃.insideBudget X q i) → X) → ℕ → X :=
    fun tY c => sourceEntry (PRG.Rand.law1 X) tY c
  -- The lazy dictionary on a table of values `L*[X]` for the queries' ranks.
  let LD : (Fin (q .eval) → X) → Resource (Queries X q) := fun t =>
    Resource.ofAutomaton (Queries X q) (lazyDictionary (Queries X q) (𝓡₃.law1 X) t
      (fun _ x => x) (fun _ _ z => z)) (Distribution.ProbDist.single [])
  -- On the tables `(tY, tZ)`, `𝓡₃` is the lazy dictionary on the values `L₂[ys r]`.
  have dict : ∀ t : (Fin (PRG.Rand.bound X * ∑ i, 𝓡₃.insideBudget X q i) → X) ×
      (Fin (𝓡₃.bound X * ∑ i, q i) → X),
      Resource.ofAutomaton (Queries X q)
        ((𝓡₃.body X).combine (parallelStep ((PRG.Rand.body X).combine
          (sourceStep (PRG.Rand.law1 X)) (PRG.Rand.bound_spec X)) (sourceStep (𝓡₃.law1 X)))
          (𝓡₃.bound_spec X))
        (Distribution.ProbDist.single (none, ((none, (t.1, 0)), (t.2, 0)))) =
      LD (fun r => valueLstar (𝓡₃.law1 X) t.2 (ys t.1) r) := by
    intro t
    -- `samp-rand` after `c` calls: at the position `c` of `tY`.
    let stB : ℕ → Option Unit × ((Fin (PRG.Rand.bound X * ∑ i, 𝓡₃.insideBudget X q i) → X) × ℕ)
      | 0 => (none, (t.1, 0))
      | c + 1 => (some (), (t.1, c + 1))
    -- Its `c`-th call answers the entry `c` of `tY`.
    have hB : ∀ c, (PRG.Rand.body X).combine (sourceStep (PRG.Rand.law1 X))
        (PRG.Rand.bound_spec X) (stB c) .eval () = (stB (c + 1), ys t.1 c) := by
      rintro (_ | c)
      · exact PRG.Rand.combine_eq _ _ _
      · exact PRG.Rand.combine_eq _ _ _
    -- So `𝓡₃` on the tables is the lazy dictionary on the values `L₂[ys r]`.
    exact 𝓡₃_combine_eq_lazyDictionary X _ q stB (ys t.1) hB t.2
  -- `𝓡₃`'s table is long enough: `2q ≥ q` entries.
  have long : q .eval ≤ 𝓡₃.bound X * ∑ i, q i := by
    simp only [𝓡₃.bound, Fintype.sum_unique]; exact Nat.le_mul_of_pos_left _ two_pos
  -- **`L₂` is a uniform function on the `Y`s**: for each `tY`, the values `L₂[ys r]` filled from
  -- a uniform table `tZ` have the law of `T₂(ys r)` for a uniform `T₂`. Both read independent
  -- uniform values at the distinct `Y`s, `tZ` at their ranks and `T₂` at the `Y`s themselves.
  have hlaw : ∀ tY, Distribution.fTransform
      (fun tZ => fun r : Fin (q .eval) => valueLstar (𝓡₃.law1 X) tZ (ys tY) r)
      (Distribution.pi fun _ : Fin (𝓡₃.bound X * ∑ i, q i) => (𝓡₃.law1 X).1) =
      Distribution.fTransform (fun T₂ : X → X => fun r : Fin (q .eval) => T₂ (ys tY r))
        (Distribution.uniform (X → X)) := by
    intro tY
    -- The distinct `Y`s of the `q` calls.
    let F := keysL₂ (ys tY) (q .eval)
    -- The rank of `ys r` among the keys after `r + 1` calls is its rank among all of them.
    have rank : ∀ r : Fin (q .eval),
        (keysL₂ (ys tY) (r + 1)).idxOf (ys tY r) = F.idxOf (ys tY r) := by
      intro r
      -- The `q` calls are the first `r + 1`, then the others.
      have split : List.range (q .eval) = List.range ((r : ℕ) + 1) ++
          (List.range (q .eval - ((r : ℕ) + 1))).map (((r : ℕ) + 1) + ·) := by
        rw [← List.range_add]; congr 1; omega
      simp only [F, keysL₂, split, List.map_append]
      -- The rank of a key among the first occurrences does not change as answers are appended.
      exact (List.idxOf_firstOccurrences_append (ks := (List.range ((r : ℕ) + 1)).map (ys tY))
        (k := ys tY r) (List.mem_map.mpr ⟨r, by simp, rfl⟩) _).symm
    -- Every answer is one of the `Y`s.
    have mem : ∀ r : Fin (q .eval), ys tY r ∈ F := fun r =>
      List.mem_firstOccurrences.mpr (List.mem_map.mpr ⟨r, by simp, rfl⟩)
    -- Compare the two laws at every table `v` of values.
    ext v
    rw [Distribution.fTransform_apply_eq_mass, Distribution.fTransform_apply_eq_mass,
      ← Distribution.pi_uniform]
    -- The table `tZ` read at the ranks of the distinct `Y`s, against independent samples at
    -- every `Y`, for the event "the values at the answers are `v`" (it reads only the `Y`s).
    refine (Distribution.mass_congr _ fun tZ => ?_).trans
      (Distribution.mass_pi_sourceEntry_idxOf (𝓡₃.law1 X) F (List.nodup_firstOccurrences _) ?_
        (fun T₂ => (fun r : Fin (q .eval) => T₂ (ys tY r)) = v) ?_)
    · -- `L₂[ys r]` is the entry of `tZ` at the rank of `ys r` among all the `Y`s.
      simp only [valueLstar, rank]
    · -- (At most `q` distinct `Y`s, and `tZ` has `2q` entries.)
      simp only [F, keysL₂]
      rw [List.length_firstOccurrences]
      exact (List.toFinset_card_le _).trans (by simpa using long)
    · -- The event reads the function only at the answers, which are among the `Y`s.
      intro s s' hs
      simp only [funext_iff]
      exact forall_congr' fun r => by rw [hs _ (mem r)]
  -- For each `T₂`, the lazy dictionary on `T₂(ys ·)` is the lazy dictionary on the table `tY`
  -- answering `T₂` at its entries: both answer the query of rank `r` with `T₂(tY r)`.
  have answer : ∀ (T₂ : X → X) tY, LD (fun r => T₂ (ys tY r)) =
      Resource.ofAutomaton (Queries X q) (lazyDictionary (Queries X q) (PRG.Rand.law1 X) tY
        (fun _ x => x) (fun _ _ y => T₂ y)) (Distribution.ProbDist.single []) := by
    intro T₂ tY
    -- The same dictionary of inputs on both sides, with at most as many inputs as queries.
    refine Resource.ofAutomaton_single_congr_on_domain
      (fun h D D' => D = D' ∧ D.length ≤ h.length) ⟨rfl, le_rfl⟩ ?_
    rintro h ⟨⟨⟩, x⟩ D _ hd ⟨rfl, hlen⟩
    -- The history has fewer than `q` queries.
    have hq : h.length < q .eval := by
      simpa using evaluation_length_le (q := q) (Or.inr hd)
    -- The dictionary after `x` has at most one more input, ...
    have hD : (if x ∈ D then D else D ++ [x]).length ≤ h.length + 1 := by
      split_ifs <;> simp <;> omega
    -- ... so the rank of `x` is below `q`.
    have hr : (if x ∈ D then D else D ++ [x]).idxOf x < q .eval :=
      ((List.idxOf_lt_length_of_mem (by split_ifs with hx <;> simp [hx])).trans_le hD).trans_le
        (by omega)
    -- Same answer, same dictionary, and one more input at most for one more query.
    refine ⟨?_, rfl, ?_⟩
    swap
    · show (if x ∈ D then D else D ++ [x]).length ≤ (h ++ [_]).length
      simpa using hD
    -- Below `q`, the table `T₂(ys ·)` at the rank is `T₂` at the entry of `tY`.
    simp only [lazyDictionary]
    exact sourceEntry_of_lt (𝓡₃.law1 X) (fun r : Fin (q .eval) => T₂ (ys tY r)) hr
  -- At most `q` distinct inputs.
  have distinct : ∀ h, (Queries X q).domain h →
      (h.map fun x => x.2).toFinset.card ≤ q .eval := fun h hd =>
    (List.toFinset_card_le _).trans
      ((List.length_map _).trans_le (evaluation_length_le (Or.inr hd)))
  calc _ = Resource.sample (Distribution.prod (Distribution.pi fun _ => (PRG.Rand.law1 X).1)
        (Distribution.pi fun _ => (𝓡₃.law1 X).1))
        (fun t => LD (fun r => valueLstar (𝓡₃.law1 X) t.2 (ys t.1) r)) := by
        -- On each pair of tables, the lazy dictionary on the values `L*[X]`.
        congr 1; funext t; exact dict t
    _ = Resource.sample (Distribution.pi fun _ => (PRG.Rand.law1 X).1) (fun tY =>
          Resource.sample (Distribution.pi fun _ => (𝓡₃.law1 X).1)
            (fun tZ => LD (fun r => valueLstar (𝓡₃.law1 X) tZ (ys tY) r))) :=
        -- Sampling the pair is sampling `tY`, then `tZ`.
        (Resource.sample_sample _ _
          (fun tY tZ => LD (fun r => valueLstar (𝓡₃.law1 X) tZ (ys tY) r))).symm
    _ = Resource.sample (Distribution.pi fun _ => (PRG.Rand.law1 X).1) (fun tY =>
          Resource.sample (Distribution.uniform (X → X))
            (fun T₂ => LD (fun r => T₂ (ys tY r)))) := by
        -- For each `tY`, `L₂` filled from `tZ` is a uniform function `T₂` on the `Y`s (`hlaw`).
        congr 1; funext tY
        exact (Resource.sample_fTransform
          (fun tZ => fun r : Fin (q .eval) => valueLstar (𝓡₃.law1 X) tZ (ys tY) r) _ LD).symm.trans
          ((Resource.sample_congr_law (hlaw tY) LD).trans (Resource.sample_fTransform _ _ LD))
    _ = Resource.sample (Distribution.uniform (X → X)) (fun T₂ =>
          Resource.sample (Distribution.pi fun _ => (PRG.Rand.law1 X).1)
            (fun tY => LD (fun r => T₂ (ys tY r)))) :=
        -- `tY` and `T₂` are independent: sample `T₂` first.
        Resource.sample_comm _ _ _
    _ = Resource.sample (Distribution.uniform (X → X)) (fun T₂ =>
          Resource.sample (Distribution.pi fun _ : X => (PRG.Rand.law1 X).1)
            (fun T₁ => Resource.ofFunction fun _ x => T₂ (T₁ x))) := by
        -- For each `T₂`: the lazy dictionary `L₁` on the table `tY`, answered through `T₂`, is
        -- `T₂ ∘ T₁` for independent uniform values `T₁` at every input (lazy sampling).
        congr 1; funext T₂
        simp only [answer]
        exact Resource.sample_lazyDictionary _ _ _ _ fun h hd => (distinct h hd).trans
          (by simp only [PRG.Rand.bound, one_mul, Fintype.sum_unique]; exact le_rfl)
    _ = Resource.sample (Distribution.uniform (X → X)) (fun T₂ =>
          Resource.sample (Distribution.uniform (X → X))
            (fun T₁ => Resource.ofFunction fun _ x => T₂ (T₁ x))) := by
        -- Independent uniform values at every input are a uniform function.
        congr 1; funext T₂; exact Resource.sample_congr_law Distribution.pi_uniform _
    _ = composedURF X := by
        -- Sampling `T₂`, then `T₁`, is sampling the uniform pair `(T₁, T₂)`.
        rw [Resource.sample_comm, Resource.sample_sample, composedURF]
        exact Resource.sample_congr_law Distribution.prod_uniform _

variable (X) in
/-- **With distinct `Y`s the inner condition is always taken** [1, §2]: for `q ≤ |X|`, `𝓡₃` on
`samp-uniq` is `prf-rand^H`, the uniform random function. Every new input gets a fresh `L₂[Y]`,
a new uniform value. -/
lemma 𝓡₃_smul_sampUniq (q : Evaluation.Port → ℕ) (fits : q .eval ≤ Fintype.card X) :
    𝓡₃.perPort X (budget := q) • SampUniq.perPort X (budget := 𝓡₃.insideBudget X q) =
      URF (Queries X q) := by
  classical
  --   D ─ 𝓡₃ (L*, L₂) ─ samp-uniq:  eval(x) for a new x:  bday.eval(()) ⇒ Y, distinct;
  --                                  L₂[Y] ← 𝒰[X], always;  eval ⇒ L₂[Y]
  --   D ─ prf-rand^H:                eval(x) ⇒ L[x], L[x] ← 𝒰[X] for a new x
  --
  -- `samp-uniq` is its program run on its table of orderings.
  unfold SampUniq.perPort Converter.ofProgram SampUniq.randomness Resource.source
  rw [ofDDC_ofProgramOn_smul_ofAutomaton_pi (A := Evaluation.perPort Unit X (𝓡₃.insideBudget X q))
    (B := Interface.source (Equiv.Perm X) (SampUniq.bound X * ∑ i, 𝓡₃.insideBudget X q i))
    none (SampUniq.body X) (SampUniq.bound_spec X)]
  -- `𝓡₃` on it samples the table of orderings and its own table `tZ`.
  rw [𝓡₃_smul_ofAutomaton]
  -- `samp-uniq` answers its `c`-th call with the ordering at the `c`-th element of `X`, ...
  let e : ℕ → X := fun c => (Fintype.equivFin X).symm (Fin.ofNat (Fintype.card X) c)
  -- ... and the first `|X|` elements are distinct.
  have he : ∀ i < Fintype.card X, ∀ j < Fintype.card X, e i = e j → i = j := by
    intro i hi j hj h
    -- `e i = e j` gives `i mod |X| = j mod |X|`, and both are below `|X|`.
    have := congrArg Fin.val ((Fintype.equivFin X).symm.injective h)
    simpa [Fin.val_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using this
  -- On the tables, `𝓡₃` is the lazy dictionary on the entries of `tZ`: the `Y`s are distinct,
  -- so the query of rank `r` gets the fresh `L₂[Y]`, the entry `r`.
  have dict : ∀ t : (Fin (SampUniq.bound X * ∑ i, 𝓡₃.insideBudget X q i) → Equiv.Perm X) ×
      (Fin (𝓡₃.bound X * ∑ i, q i) → X),
      Resource.ofAutomaton (Queries X q)
        ((𝓡₃.body X).combine (parallelStep ((SampUniq.body X).combine
          (sourceStep (SampUniq.law1 X)) (SampUniq.bound_spec X)) (sourceStep (𝓡₃.law1 X)))
          (𝓡₃.bound_spec X))
        (Distribution.ProbDist.single (none, ((none, (t.1, 0)), (t.2, 0)))) =
      Resource.ofAutomaton (Queries X q)
        (lazyDictionary (Queries X q) (𝓡₃.law1 X)
          (fun r : Fin (q .eval) => sourceEntry (𝓡₃.law1 X) t.2 r) (fun _ x => x)
          (fun _ _ z => z))
        (Distribution.ProbDist.single []) := by
    intro t
    -- The ordering, read from the table at the first call.
    let σ := sourceEntry (SampUniq.law1 X) t.1 0
    -- `samp-uniq` after `c` calls: nothing stored before the first, then `(σ, c)`.
    let stB : ℕ → Option (Equiv.Perm X × ℕ) ×
        ((Fin (SampUniq.bound X * ∑ i, 𝓡₃.insideBudget X q i) → Equiv.Perm X) × ℕ)
      | 0 => (none, (t.1, 0))
      | c + 1 => (some (σ, c + 1), (t.1, 1))
    -- Its `c`-th call answers `σ(e c)`.
    have hB : ∀ c, (SampUniq.body X).combine (sourceStep (SampUniq.law1 X))
        (SampUniq.bound_spec X) (stB c) .eval () = (stB (c + 1), σ (e c)) := by
      rintro (_ | c)
      · exact SampUniq.combine_first X t.1 0
      · exact SampUniq.combine_later X σ (c + 1) (t.1, 1)
    -- `𝓡₃` is the lazy dictionary on the values `L₂[σ(e r)]`; compare the tables entrywise.
    rw [𝓡₃_combine_eq_lazyDictionary X _ q stB (fun c => σ (e c)) hB t.2]
    congr 3
    funext r
    -- The answers `σ(e 0), σ(e 1), …` below `q ≤ |X|` are distinct, so `L₂[σ(e r)]` is the
    -- fresh entry `r`.
    refine valueLstar_of_injective _ _ _ fun i hi j hj h => he i (by omega) j (by omega)
      (σ.injective h)
  -- `𝓡₃`'s table is long enough: `2q ≥ q` entries.
  have short : q .eval ≤ 𝓡₃.bound X * ∑ i, q i := by
    simp only [𝓡₃.bound, Fintype.sum_unique]; exact Nat.le_mul_of_pos_left _ two_pos
  -- The first `q` entries of `tZ` are `q` independent uniform values; the orderings are unused.
  have hlaw : Distribution.fTransform
      (fun t : (Fin (SampUniq.bound X * ∑ i, 𝓡₃.insideBudget X q i) → Equiv.Perm X) ×
        (Fin (𝓡₃.bound X * ∑ i, q i) → X) =>
          fun r : Fin (q .eval) => sourceEntry (𝓡₃.law1 X) t.2 r)
      (Distribution.prod (Distribution.pi fun _ => (SampUniq.law1 X).1)
        (Distribution.pi fun _ => (𝓡₃.law1 X).1)) =
      Distribution.pi fun _ : Fin (q .eval) => (𝓡₃.law1 X).1 := by
    -- Reading the first `q` entries of `tZ` is restricting `tZ` along `Fin q ↪ Fin 2q`.
    have read : (fun t : (Fin (SampUniq.bound X * ∑ i, 𝓡₃.insideBudget X q i) → Equiv.Perm X) ×
        (Fin (𝓡₃.bound X * ∑ i, q i) → X) =>
          fun r : Fin (q .eval) => sourceEntry (𝓡₃.law1 X) t.2 r) =
        (fun tZ => tZ ∘ Fin.castLE short) ∘ Prod.snd := by
      -- The entry `r < q ≤ 2q` of the table.
      funext t r
      exact sourceEntry_of_lt _ _ (r.isLt.trans_le short)
    -- The second component of the pair of tables is `tZ`, of the uniform table law (the table
    -- of orderings has weight `1`) ...
    rw [read, ← Distribution.fTransform_comp, Distribution.fTransform_snd_prod,
      Distribution.weight_pi]
    simp only [(SampUniq.law1 X).2.2, Finset.prod_const_one, one_smul]
    -- ... and independent samples restricted along an injection are independent samples.
    exact Distribution.fTransform_pi_comp_injective _ (𝓡₃.law1 X).2.2 _ (Fin.castLE_injective short)
  -- At most `q` distinct inputs.
  have distinct : ∀ h, (Queries X q).domain h →
      (h.map fun x => x.2).toFinset.card ≤ q .eval := fun h hd =>
    (List.toFinset_card_le _).trans
      ((List.length_map _).trans_le (evaluation_length_le (Or.inr hd)))
  calc _ = Resource.sample (Distribution.prod (Distribution.pi fun _ => (SampUniq.law1 X).1)
        (Distribution.pi fun _ => (𝓡₃.law1 X).1)) (fun t => Resource.ofAutomaton (Queries X q)
          (lazyDictionary (Queries X q) (𝓡₃.law1 X)
            (fun r : Fin (q .eval) => sourceEntry (𝓡₃.law1 X) t.2 r) (fun _ x => x)
            (fun _ _ z => z)) (Distribution.ProbDist.single [])) := by
        -- On each pair of tables, the lazy dictionary on the entries of `tZ`.
        congr 1
        funext t
        exact dict t
    _ = Resource.sample (Distribution.pi fun _ : Fin (q .eval) => (𝓡₃.law1 X).1) (fun t =>
          Resource.ofAutomaton (Queries X q) (lazyDictionary (Queries X q) (𝓡₃.law1 X) t
            (fun _ x => x) (fun _ _ z => z)) (Distribution.ProbDist.single [])) :=
        -- It reads only the first `q` entries of `tZ`, `q` independent uniform values.
        Resource.sample_eq_sample_of_fTransform _ _ _ _ _ hlaw fun _ => rfl
    _ = Resource.sample (Distribution.pi fun _ : X => (𝓡₃.law1 X).1)
          (fun s => Resource.ofFunction fun _ x => s x) :=
        -- Lazy sampling: the lazy dictionary on a table of uniform values is a function with
        -- independent uniform values at every input.
        Resource.sample_lazyDictionary _ _ _ _ distinct
    _ = URF (Queries X q) := by
        -- Independent uniform values at every input are the uniform random function.
        rw [URF_perPort_eq]
        exact Resource.sample_congr_law Distribution.pi_uniform _

variable (X) in
/-- **The birthday maneuver** [1, §2]: after the two swaps, the hybrid is within `q(q-1)/(2|X|)`
of `prf-rand^H`. With `L₁` eliminated, `Y := bday.samp()` through `𝓡₃`, the birthday lemma swaps
`samp-rand` for `samp-uniq`, and with distinct `Y`s the hybrid is `prf-rand^H`. Past `|X|`
queries the bound is at least `1`. -/
lemma birthday_maneuver (q : Evaluation.Port → ℕ) :
    Δ (𝓡₂.perPort X (budget := q) • URF (Queries X q)) (URF (Queries X q)) ≤
      ENNReal.ofReal ((q .eval : ℝ) * ((q .eval : ℝ) - 1) / (2 * Fintype.card X)) := by
  by_cases fits : q .eval ≤ Fintype.card X
  swap
  · -- More than `|X|` queries: `q(q-1)/(2|X|) ≥ 1` bounds every distance.
    exact distance_le_birthday_of_card_lt X _ _ (not_le.mp fits)
  -- At most `|X|` queries: the notes' hybrids, as systems (the distinguisher D on the left).
  --
  --   D ─ 𝓡₂ ─ prf-rand^F     =                 inline L₂             𝓡₂_smul_urf
  --   D ─ T₂ ∘ T₁             =                 eliminate L₁          𝓡₃_smul_prgRand
  --   D ─ 𝓡₃ ─ samp-rand      ≈[q(q-1)/2|X|]    birthday lemma
  --   D ─ 𝓡₃ ─ samp-uniq      =                 inner if taken        𝓡₃_smul_sampUniq
  --   D ─ prf-rand^H
  cc_calc statistical
    -- inline the uniform random function `L₂`: the two dictionaries as uniform functions
    𝓡₂.perPort X • URF (Queries X q) = composedURF X := 𝓡₂_smul_urf X q
    -- eliminate `L₁`: a fresh `Y` per new input, drawn from `bday.samp()` in `samp-rand`
    _ = 𝓡₃.perPort X (budget := q) • PRG.Rand.perPort X (budget := 𝓡₃.insideBudget X q) :=
      (𝓡₃_smul_prgRand X q).symm
    -- the birthday lemma inside the context `𝓡₃`: attaching a converter does not increase the
    -- distance, and `samp-rand` is within `q(q-1)/(2|X|)` of `samp-uniq` at `q` samples
    _ ≈[ENNReal.ofReal ((q .eval : ℝ) * ((q .eval : ℝ) - 1) / (2 * Fintype.card X))]
        𝓡₃.perPort X (budget := q) • SampUniq.perPort X (budget := 𝓡₃.insideBudget X q) :=
      (distance_smul_le _ _ _).trans (prgRand_sampUniq_distance_le X _)
    -- with distinct `Y`s every `L₂[Y]` is fresh: the uniform random function
    _ = URF (Queries X q) := 𝓡₃_smul_sampUniq X q fits

/-! ### The theorem -/

variable {K : Type} [Fintype K] [Nonempty K]

/-- **PRF cascade** [1, §2]: if `F` is a secure PRF within `ε`, then the cascade is a secure PRF
within the losses of the two swaps and the birthday bound `q(q-1)/(2|X|)`. -/
theorem prf_cascade [AdmissibleDistinguishers] (F : K → X → X) {q : Evaluation.Port → ℕ}
    (ε : (Queries X q).inputDomain.DistinguisherBehavior → ENNReal) (secure : PRF.Secure F ε) :
    PRF.Secure (H F) fun D =>
      ε (absorb (𝓡₁.perPort F) D) + ε (absorb (𝓡₂.perPort X) D) +
        ENNReal.ofReal ((q .eval : ℝ) * ((q .eval : ℝ) - 1) / (2 * Fintype.card X)) := by
  -- The notes' hybrids [1, §2], as systems (the distinguisher D on the left):
  --
  --   D ─ prf-real^H                                 start
  --   D ─ 𝓡₁ ─ prf-real^F     =                      separate K₁, K₂     𝓡₁_smul_prfReal
  --   D ─ 𝓡₁ ─ prf-rand^F     ≃[ε(D ∘ 𝓡₁)]           swap F(K₁, ·) for L₁: PRF security of F
  --   D ─ 𝓡₂ ─ prf-real^F     =                      factor out F(K₂, ·)  𝓡₁_smul_urf
  --   D ─ 𝓡₂ ─ prf-rand^F     ≃[ε(D ∘ 𝓡₂)]           swap F(K₂, ·) for L₂: PRF security of F
  --   D ─ prf-rand^H          ≈[q(q-1)/(2|X|)]       the birthday maneuver  birthday_maneuver
  --
  -- `cc_calc` chains `=`, `≃[·]` and `≈[·]` steps for the admitted distinguishers; the losses
  -- add up. Its first line names the distinguishing advantage, and how it is bounded by the
  -- distance.
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    -- separate `K₁` from `K₂`: the second key is sampled in the calling program `𝓡₁`
    PRF.Real (H F) = 𝓡₁.perPort F • PRF.Real F := (𝓡₁_smul_prfReal F q).symm
    -- swap `F(K₁, ·)` for `L₁` inside `𝓡₁`: the PRF assumption at `D ∘ 𝓡₁`
    _ ≃[fun D => ε (absorb (𝓡₁.perPort F) D)] 𝓡₁.perPort F • URF (Queries X q) :=
      AdmissibleDistinguishers.substitutesWithin_attach _ secure
    -- inline `L₁`, factor out `F(K₂, ·)` into `prf-real^F`, with the calling program `𝓡₂`
    _ = 𝓡₂.perPort X • PRF.Real F := 𝓡₁_smul_urf F q
    -- swap `F(K₂, ·)` for `L₂` inside `𝓡₂`: the PRF assumption at `D ∘ 𝓡₂`
    _ ≃[fun D => ε (absorb (𝓡₂.perPort X) D)] 𝓡₂.perPort X • URF (Queries X q) :=
      AdmissibleDistinguishers.substitutesWithin_attach _ secure
    -- the birthday maneuver: within `q(q-1)/(2|X|)` of `prf-rand^H`
    _ ≈[ENNReal.ofReal ((q .eval : ℝ) * ((q .eval : ℝ) - 1) / (2 * Fintype.card X))]
        URF (Queries X q) := birthday_maneuver X q

/-- **PRF cascade at `{0,1}^λ`** [1, §2], the notes' statement: for `F` with keys, inputs and
outputs in `{0,1}^λ`, the birthday bound is `q(q-1)/2^{λ+1}`. The security parameter `λ` is
`secpar`. -/
theorem prf_cascade_bits [AdmissibleDistinguishers] {secpar : ℕ}
    (F : Bits secpar → Bits secpar → Bits secpar) {q : Evaluation.Port → ℕ}
    (ε : (Queries (Bits secpar) q).inputDomain.DistinguisherBehavior → ENNReal)
    (secure : PRF.Secure F ε) :
    PRF.Secure (H F) fun D =>
      ε (absorb (𝓡₁.perPort F) D) + ε (absorb (𝓡₂.perPort (Bits secpar)) D) +
        ENNReal.ofReal ((q .eval : ℝ) * ((q .eval : ℝ) - 1) / 2 ^ (secpar + 1)) := by
  -- `|{0,1}^λ| = 2^λ`, and `2 · 2^λ = 2^{λ+1}`.
  simpa only [card_bits, Nat.cast_pow, Nat.cast_ofNat, ← pow_succ'] using prf_cascade F ε secure

end

end ProofLadders.PRFCascade.CodeBased
