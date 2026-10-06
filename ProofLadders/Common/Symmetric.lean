import Commons.Definitions.Ideal
import ConstructiveCryptography.Notation
import ConstructiveCryptography.GameBound
import ConstructiveCryptography.Tactics.Substitution
import ProofLadders.Common.Functional
import ProofLadders.Common.LazySampling
import ProofLadders.Common.Probability

/-!
# Pseudorandom functions and generators, as libraries

The libraries of the ladder's symmetric problems [1], in the form of the library's Commons
notions: a notion is the pair of its systems, and the predicate of the same name states it for
the admitted distinguishers, `X₀ ≃[ε] X₁`.

* `prf-real^F` is `F` under a uniform key; `prf-rand^F`, the lazy random dictionary, is the
  uniform random function `URF` of `Commons.Definitions.Ideal`.
* `prg-real^G` answers each query with `G(s)` for a fresh uniform seed `s`, and `prg-rand` with a
  fresh uniform element. This is the many-sample form of [1]; Commons' `PRG.Secure` answers every
  query with one sample.
* The birthday lemma of [1, §2]: `samp-rand` is `prg-rand`, and `samp-uniq` samples without
  replacement.
* Unforgeable PRFs under many keys [2]: the keyed function, evaluated and checked under the key of
  each index, against a lazy random function whose check accepts only evaluated points.
* Sampled functions: the uniform random function at per-port budgets as a sampled function;
  many-seed PRG security, a seed per index sampled once, with its relations to the libraries of a
  fresh sample per query, by lazy sampling; sampling without replacement as a random ordering on
  the indices, and the birthday lemma in that form, as a game.

Bit strings `{0,1}^n` are `Bits n`, with pointwise addition as `⊕`; a concatenation `A ‖ B` of
two halves is the pair `(A, B)`.

Upstream candidates: `Bits` and `card_bits` for `Commons.Schemes.Bytes`; `PRF.Real`,
`PRF.Secure.systems`, `PRF.Secure`, `Checking`, `PRF.Keys`, `PRF.UnforgeableRF`,
`PRF.EUF.systems` and `PRF.EUF` for a new module `Commons.Definitions.PRF`; `PRG.Real`,
`PRG.Rand`, `PRG.Samples.systems` and `PRG.Samples`, `PRG.SeedsReal`, `PRG.Seeds.systems`,
`PRG.Seeds`, `PRG.Lazy`, `Index`, `prgSeeds_of_prgSamples`, `prgReal_eq_index` and
`prgRand_eq_index`, with their steps `PRG.Lazy.combine_eq`, `PRG.Lazy.smul_source`,
`PRG.Lazy.smul_real`, `PRG.Lazy.smul_rand`, `Index.combine_eq`, `Index.smul_ofFunction`,
`PRG.Real.combine_eq` and `PRG.Rand.combine_eq`, for `Commons.Definitions.PRG`; `SampUniq`,
`prgRand_sampUniq_distance_le`, `distance_le_birthday_of_card_lt`, `evaluation_length_le`,
`URF_eq_sample`, `URF_perPort_eq` (`cbc-mac-cc`'s `URF_eq`, `CBCMAC/RandomnessExpander.lean`, at
per-port budgets), `URF_perPort_eq_ofAutomaton`,
`orderedSamples`, `sampUniq_eq_index` with its steps `SampUniq.combine_first` and
`SampUniq.combine_later`, `Repeated`, `birthdayGame`, `birthday_game_equiv`,
`birthdayGame_blind_bound` and `urf_orderedSamples_distance_le` for `Commons.Definitions.Ideal`.

## Main definitions

* `Bits n`: bit strings of length `n`
* `PRF.Real F`, `PRF.Secure.systems F q`, `PRF.Secure F error`: PRF security
* `PRG.Real G`, `PRG.Rand R`, `PRG.Samples.systems G q`, `PRG.Samples G error`: PRG security
  with a fresh seed per sample
* `SampUniq X`: sampling without replacement
* `Checking I X Y`, `PRF.EUF.systems F I q`, `PRF.EUF F I error`: unforgeable PRFs under the keys
  of the indices `I`
* `PRG.SeedsReal G P`, `PRG.Seeds.systems G P q`, `PRG.Seeds G P error`: many-seed PRG security
* `PRG.Lazy P R`, `Index R n`: seeds from fresh samples, and fresh samples from indexed ones
* `orderedSamples X n`, `birthdayGame X n q`: samples without replacement, indexed, and the
  birthday game

## Main results

* `prgRand_sampUniq_distance_le`: the birthday lemma, `samp-rand ≈ samp-uniq` within
  `q(q-1)/(2|X|)`
* `distance_le_birthday_of_card_lt`: past `|X|` samples the birthday bound is at least `1`
* `card_bits`, `evaluation_length_le`: `2^n` bit strings, and at most `q` queries on `q`
* `URF_eq_sample`, `URF_perPort_eq`: the uniform random function samples a function once
* `URF_perPort_eq_ofAutomaton`: the uniform random function is the automaton holding a uniform
  function
* `prgSeeds_of_prgSamples`: many-seed PRG security from fresh-seed PRG security
* `PRG.Lazy.smul_source`, `PRG.Lazy.smul_real`, `PRG.Lazy.smul_rand`: `PRG.Lazy` on a library of
  fresh samples is the lazy random dictionary, on `prg-real^G` it is `G` on a seed per index, on
  `prg-rand` the uniform random function
* `prgReal_eq_index`, `prgRand_eq_index`, `sampUniq_eq_index`: the fresh-sample libraries are the
  indexed ones, counted
* `birthday_game_equiv`, `birthdayGame_blind_bound`, `urf_orderedSamples_distance_le`: the
  birthday lemma, indexed

## References

1. The symmetric proof ladder, *Security proofs in the style of The Joy of Cryptography*,
   `proof-ladders/symmetric-ladder`, `Notes/selfcontained.tex`.
2. The protocol ladder, Basic Hash in EasyCrypt, `basic-hash/EasyCrypt/basic-hash-unlink.ec`.
-/

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

/-- Bit strings `{0,1}^n`, with pointwise addition as `⊕`. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- There are `2^n` bit strings of length `n`. -/
lemma card_bits (n : ℕ) : Fintype.card (Bits n) = 2 ^ n := by
  simp [Bits]

noncomputable section

/-! ## Pseudorandom functions -/

section PRF

variable {K X Y : Type} [Fintype K] [Nonempty K] [Fintype X] [Fintype Y] [Nonempty Y]

/-- **`prf-real^F`** [1, §2]: `F` under a uniform key `k`, answering each input `X` with
`F(k, X)`. -/
def PRF.Real (F : K → X → Y) {q : Evaluation.Port → ℕ} :
    Interface.Resource (Evaluation.perPort X Y q) :=
  Interface.Resource.sample (Distribution.uniform K) fun k =>
    Interface.Resource.ofFunction fun _ x => F k x

/-- **The systems of PRF security**: `prf-real^F` and `prf-rand^F`, the uniform random function,
at the budget `q`. -/
def PRF.Secure.systems (F : K → X → Y) (q : Evaluation.Port → ℕ) :
    Interface.Resource (Evaluation.perPort X Y q) ×
      Interface.Resource (Evaluation.perPort X Y q) :=
  (PRF.Real F, URF (Evaluation.perPort X Y q))

/-- **PRF security** within `error`: against the admitted distinguishers, `prf-real^F`
substitutes for `prf-rand^F`. -/
def PRF.Secure [Interface.AdmissibleDistinguishers] (F : K → X → Y) {q : Evaluation.Port → ℕ}
    (error : (Evaluation.perPort X Y q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (PRF.Secure.systems F q).1 ≃[error] (PRF.Secure.systems F q).2

end PRF

interface Checking(I X Y : Type) [Fintype I] [Fintype X] [Fintype Y]
  f(i : I, x : X) → Y
  check(i : I, x : X, s : Y) → Bool

section EUF

variable {K X Y : Type} [Fintype K] [Fintype X] [Fintype Y]

-- `PRFs` [2]: a uniform key `k_i` for every index `i`; `f(i, x)` returns `F(k_i, x)` and
-- `check(i, x, s)` returns `[F(k_i, x) = s]`.
system PRF.Keys(F : K → X → Y) (I : Type) [Fintype I] [DecidableEq I] [Nonempty K] [DecidableEq Y] : Checking I X Y
  initialize
    keys ←$ 𝒰[I → K]
  on f(i : I, x : X) → Y
    return F (keys i) x
  on check(i : I, x : X, s : Y) → Bool
    return decide (F (keys i) x = s)

-- `EUF_RF` [2]: a lazy random function `T`; `f(i, x)` returns `T(i, x)`, and `check(i, x, s)`
-- accepts only if `(i, x)` was evaluated and `T(i, x) = s`.
system PRF.UnforgeableRF(I X Y : Type) [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y] : Checking I X Y
  initialize
    T ←$ 𝒰[I × X → Y]
    evaluated ← ([] : List (I × X))
  on f(i : I, x : X) → Y
    evaluated ← evaluated ++ [(i, x)]
    return T (i, x)
  on check(i : I, x : X, s : Y) → Bool
    return decide ((i, x) ∈ evaluated ∧ T (i, x) = s)

variable [Nonempty K] [Nonempty Y] [DecidableEq X] [DecidableEq Y]

/-- **The systems of unforgeable PRFs** [2]: `F` under the keys of the indices `I`, and the lazy
random function that checks only evaluated points, at the budget `q` per port. -/
def PRF.EUF.systems (F : K → X → Y) (I : Type) [Fintype I] [DecidableEq I]
    (q : Checking.Port → ℕ) :
    Interface.Resource (Checking.perPort I X Y q) × Interface.Resource (Checking.perPort I X Y q) :=
  (PRF.Keys.perPort F I, PRF.UnforgeableRF.perPort I X Y)

/-- **Unforgeable PRFs** within `error`: against the admitted distinguishers, `F` under the keys
of the indices `I` substitutes for the lazy random function that checks only evaluated points. -/
def PRF.EUF [Interface.AdmissibleDistinguishers] (F : K → X → Y) (I : Type) [Fintype I]
    [DecidableEq I] {q : Checking.Port → ℕ}
    (error : (Checking.perPort I X Y q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (PRF.EUF.systems F I q).1 ≃[error] (PRF.EUF.systems F I q).2

end EUF

/-! ## Pseudorandom generators -/

section PRG

variable {S R : Type} [Fintype S] [Fintype R]

-- `prg-real^G`: on `samp()`, sample a fresh seed `s` and output `G(s)`.
system PRG.Real(G : S → R) [Nonempty S] : Evaluation Unit R
  on eval(_input : Unit) → R
    seed ←$ 𝒰[S]
    return G seed

-- `prg-rand`: on `samp()`, output a fresh uniform element of `R`.
system PRG.Rand(R : Type) [Fintype R] [Nonempty R] : Evaluation Unit R
  on eval(_input : Unit) → R
    y ←$ 𝒰[R]
    return y

variable [Nonempty S] [Nonempty R]

/-- **The systems of PRG security** [1, §1]: `prg-real^G` and `prg-rand`, at the budget `q`. -/
def PRG.Samples.systems (G : S → R) (q : Evaluation.Port → ℕ) :
    Interface.Resource (Evaluation.perPort Unit R q) ×
      Interface.Resource (Evaluation.perPort Unit R q) :=
  (PRG.Real.perPort G, PRG.Rand.perPort R)

/-- **PRG security** within `error`, with a fresh seed per sample: against the admitted
distinguishers, `prg-real^G` substitutes for `prg-rand`. -/
def PRG.Samples [Interface.AdmissibleDistinguishers] (G : S → R) {q : Evaluation.Port → ℕ}
    (error : (Evaluation.perPort Unit R q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (PRG.Samples.systems G q).1 ≃[error] (PRG.Samples.systems G q).2

end PRG

/-! ## The birthday lemma -/

-- `samp-uniq` [1, §2]: each sample is uniform among the values not sampled before. Sampling
-- laws are closed, so the `k`-th sample is the `k`-th value of a uniformly random ordering.
system SampUniq(X : Type) [Fintype X] [DecidableEq X] [Nonempty X] : Evaluation Unit X
  initialize
    ordering ←$ 𝒰[Equiv.Perm X]
    count ← (0 : ℕ)
  on eval(_input : Unit) → X
    next ← ordering ((Fintype.equivFin X).symm (Fin.ofNat (Fintype.card X) count))
    count ← count + 1
    return next

/-! ## Sampled functions

In the sampled-function model a library is a function sampled once and answered
deterministically. The uniform random function at per-port budgets is a sampled function. The
many-seed form of PRG security samples a seed for every index `p ∈ P` once and answers `p` with
`G(s_p)`, against the uniform random function on `P`; [1, §3] uses it with the prefixes of the
GGM tree as indices. Two converters relate it to the libraries with a fresh sample per query:
`PRG.Lazy` gives each index its seed from a fresh sample on its first query, and `Index` answers
the `k`-th query with the library at the index `k`. Sampling without replacement, indexed, is a
random ordering sampled once. -/

/-- A history admitted by the one-port interface `Evaluation X Y` at the budget `q` has at most
`q` queries. -/
lemma evaluation_length_le {X Y : Type} [Fintype X] [Fintype Y] {q : Evaluation.Port → ℕ}
    {xs : List (Σ i, (Evaluation.perPort X Y q).X i)}
    (h : xs = [] ∨ (Evaluation.perPort X Y q).domain xs) : xs.length ≤ q .eval := by
  rcases h with rfl | h
  · exact Nat.zero_le _
  · rw [length_eq_sum_restrict xs, Fintype.sum_unique]
    exact h.2 _

/-- **The uniform random function along a bijection**: a uniform function of the interface is
`e k` for a uniform `k`. -/
lemma URF_eq_sample (A : Interface) [∀ i, Nonempty (A.Y i)] {K : Type} [Fintype K]
    [Nonempty K] (e : K ≃ ∀ i, A.X i → A.Y i) :
    URF A = Interface.Resource.sample (Distribution.uniform K)
      fun k => Interface.Resource.ofFunction (e k) := by
  rw [URF]
  convert Interface.Resource.sample_uniform_equiv e Interface.Resource.ofFunction

/-- **The uniform random function samples a function once**: `cbc-mac-cc`'s `URF_eq`
(`CBCMAC/RandomnessExpander.lean`), at per-port budgets. -/
lemma URF_perPort_eq (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    {q : Evaluation.Port → ℕ} :
    URF (Evaluation.perPort X Y q) =
      Interface.Resource.sample (Distribution.uniform (X → Y))
        fun f => Interface.Resource.ofFunction fun _ => f := by
  let e : (X → Y) ≃ (∀ i, (Evaluation.perPort X Y q).X i → (Evaluation.perPort X Y q).Y i) :=
    ⟨fun f _ => f, fun F => F .eval, fun _ => rfl, fun F => funext fun i => by cases i; rfl⟩
  exact URF_eq_sample _ e

/-- **The uniform random function is an automaton** holding a uniform function `f`, sampled at the
start and kept, that answers each query `x` with `f(x)`. -/
lemma URF_perPort_eq_ofAutomaton (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y]
    [Nonempty Y] {q : Evaluation.Port → ℕ} :
    URF (Evaluation.perPort X Y q) =
      Interface.Resource.ofAutomaton (Evaluation.perPort X Y q) (fun (f : X → Y) _ x => (f, f x))
        𝒰[X → Y] := by
  -- Started on `f`, the automaton keeps `f` and answers `f(x)`: it is the function `f`.
  --   (A bisimulation with the one-state automaton of `f`: the state stays `f`.)
  have answers : ∀ f : X → Y, automatonSystem (I := (Evaluation.perPort X Y q).I)
      (X := (Evaluation.perPort X Y q).X) (Y := (Evaluation.perPort X Y q).Y)
      (fun (g : X → Y) _ x => (g, g x)) f = functionSystem fun _ => f := by
    intro f
    rw [functionSystem_eq_automatonSystem]
    refine automatonSystem_eq_of_bisim _ (rel := fun (g : X → Y) (_ : Unit) => g = f) ?_ rfl
    intro a a' i x h
    subst h
    exact ⟨rfl, rfl⟩
  -- So the automaton started on a uniform `f` is the uniform `f` sampled once, ...
  have sampled := Interface.Resource.ofAutomaton_eq_sample (A := Evaluation.perPort X Y q)
    (fun (g : X → Y) _ x => (g, g x)) (Distribution.uniform (X → Y)) id (fun f _ => f) answers
  -- ... which is the uniform random function (`URF_perPort_eq`).
  rw [URF_perPort_eq, ← sampled]
  -- (The initial law: the uniform law pushed along `id`.)
  congr 1
  exact Subtype.ext (Distribution.fTransform_id _)

section Seeds

variable {S R : Type} [Fintype S] [Nonempty S] [Fintype R] [Nonempty R]

/-- **`G` on a seed per index**: a uniform seed `s_p` for every index `p`, sampled once, and
`p` answered with `G(s_p)`. -/
def PRG.SeedsReal (G : S → R) (P : Type) [Fintype P] [DecidableEq P]
    {q : Evaluation.Port → ℕ} : Interface.Resource (Evaluation.perPort P R q) :=
  Interface.Resource.sample (Distribution.uniform (P → S))
    fun s => Interface.Resource.ofFunction fun _ p => G (s p)

/-- **The systems of many-seed PRG security**: `G` on a seed per index, and the uniform random
function on the indices `P`, at the budget `q`. -/
def PRG.Seeds.systems (G : S → R) (P : Type) [Fintype P] [DecidableEq P]
    (q : Evaluation.Port → ℕ) :
    Interface.Resource (Evaluation.perPort P R q) × Interface.Resource (Evaluation.perPort P R q) :=
  (PRG.SeedsReal G P, URF (Evaluation.perPort P R q))

/-- **Many-seed PRG security** within `error`: against the admitted distinguishers, `G` on a seed
per index substitutes for the uniform random function on the indices. -/
def PRG.Seeds [Interface.AdmissibleDistinguishers] (G : S → R) (P : Type) [Fintype P]
    [DecidableEq P] {q : Evaluation.Port → ℕ}
    (error : (Evaluation.perPort P R q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (PRG.Seeds.systems G P q).1 ≃[error] (PRG.Seeds.systems G P q).2

end Seeds

-- `PRG.Lazy`: answer each index with the sample its first query drew from `prg.samp()`.
converter PRG.Lazy(P R : Type) [Fintype P] [DecidableEq P] [Fintype R] : Evaluation P R
  inside prg : Evaluation Unit R
  initialize
    table ← ([] : List (P × R))
  on eval(p : P) → R
    match table.lookup p
    | some y →
      return y
    | none →
      y ← prg.eval(())
      table ← table ++ [(p, y)]
      return y

-- `Index`: answer the `k`-th query with `indexed.eval(k)`.
converter Index(R : Type) [Fintype R] [Nonempty R] (n : ℕ) : Evaluation Unit R
  inside indexed : Evaluation (Fin n) R
  initialize
    count ← (0 : ℕ)
  on eval(_input : Unit) → R
    match (List.finRange n).find? fun k => k.val = count
    | none →
      return Classical.arbitrary R
    | some k →
      count ← count + 1
      y ← indexed.eval(k)
      return y

section Seeds

open SystemAlgebra.Interface

variable {S R : Type} [Fintype S] [Nonempty S] [Fintype R] [Nonempty R]

/-- **`Index` against a function** `g`: the `c`-th query reads `g` at `c`, and nothing past `n`
queries. -/
lemma Index.combine_eq (n : ℕ) (g : Fin n → R) (st : Option ℕ) :
    (Index.body R n).combine (fun (_ : Unit) _ k => ((), g k)) (Index.bound_spec R n) (st, ())
        .eval () =
      if h : st.getD 0 < n then ((some (st.getD 0 + 1), ()), g ⟨st.getD 0, h⟩)
      else ((some (st.getD 0), ()), Classical.arbitrary R) := by
  split_ifs with h
  · refine Program.combine_eq_of_invoke _ _ (n := 1) ?_
    cases st <;> simp only [Option.getD] at h ⊢ <;>
      simp [Program.invoke, Index.body, callProg, returnProg, List.find?_finRange_val, h]
  · refine Program.combine_eq_of_invoke _ _ (n := 0) ?_
    cases st <;> simp only [Option.getD] at h ⊢ <;>
      simp [Program.invoke, Index.body, returnProg, List.find?_finRange_val, h]

/-- **`Index` attached to a function** is its automaton against the function. -/
lemma Index.smul_ofFunction (n : ℕ) (q : Evaluation.Port → ℕ) (g : Fin n → R) :
    Index.perPort R n (budget := q) • Resource.ofFunction (fun _ => g) =
      Resource.ofAutomaton (Evaluation.perPort Unit R q)
        ((Index.body R n).combine (fun (_ : Unit) _ k => ((), g k)) (Index.bound_spec R n))
        (Distribution.ProbDist.single (none, ())) := by
  rw [Index.perPort, Index.perPortProgram]
  exact Converter.ofPreservingProgram_smul_ofFunction _ _ _ _ _ _ _ _ _

omit [Nonempty R] in
/-- `prg-real^G` against its source: each query reads the next seed. -/
lemma PRG.Real.combine_eq (G : S → R) {k : ℕ} (st : Option Unit) (t : Fin k → S) (c : ℕ) :
    (PRG.Real.body G).combine (sourceStep (q := k) (PRG.Real.law1 G)) (PRG.Real.bound_spec G)
        (st, (t, c)) .eval () = ((some (), (t, c + 1)), G (sourceEntry (PRG.Real.law1 G) t c)) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    cases st <;>
      simp [Program.invoke, PRG.Real.body, callProg, returnProg, sourceStep, sourceEntry])

omit [Fintype S] [Nonempty S] in
/-- `prg-rand` against its source: each query reads the next sample. -/
lemma PRG.Rand.combine_eq {k : ℕ} (st : Option Unit) (t : Fin k → R) (c : ℕ) :
    (PRG.Rand.body R).combine (sourceStep (q := k) (PRG.Rand.law1 R)) (PRG.Rand.bound_spec R)
        (st, (t, c)) .eval () = ((some (), (t, c + 1)), sourceEntry (PRG.Rand.law1 R) t c) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    cases st <;>
      simp [Program.invoke, PRG.Rand.body, callProg, returnProg, sourceStep, sourceEntry])

omit [Fintype S] [Nonempty S] [Nonempty R] in
/-- `PRG.Lazy` against a library answering each query with `f` of the next entry of a table: an
index stored in the dictionary is answered from it, a new one from the library. -/
lemma PRG.Lazy.combine_eq (P : Type) [Fintype P] [DecidableEq P] {Q : Type}
    (g : Q → (j : (Evaluation Unit R 0).I) → (Evaluation Unit R 0).X j →
      Q × (Evaluation Unit R 0).Y j)
    (ls : Option (List (P × R))) (r : Q) (p : P) :
    (PRG.Lazy.body P R).combine g (PRG.Lazy.bound_spec P R) (ls, r) .eval p =
      match (ls.getD []).lookup p with
      | some y => ((some (ls.getD []), r), y)
      | none => ((some (ls.getD [] ++ [(p, (g r .eval ()).2)]), (g r .eval ()).1),
          (g r .eval ()).2) := by
  rcases hl : (ls.getD []).lookup p with _ | y
  · refine Program.combine_eq_of_invoke _ _ (n := 1) ?_
    cases ls <;> simp only [Option.getD] at hl <;>
      simp [Program.invoke, PRG.Lazy.body, callProg, returnProg, hl]
  · refine Program.combine_eq_of_invoke _ _ (n := 0) ?_
    cases ls <;> simp only [Option.getD] at hl <;>
      simp [Program.invoke, PRG.Lazy.body, returnProg, hl]

omit [Fintype S] [Nonempty S] [Nonempty R] in
/-- **`PRG.Lazy` on a library of fresh samples is the lazy random dictionary**: attached to a
library answering each query with `f` of the next entry of a table of independent samples of
`law`, it is `f` at independent samples of `law` at every index. -/
lemma PRG.Lazy.smul_source {Z : Type} [Fintype Z] [DecidableEq Z] (P : Type) [Fintype P]
    [DecidableEq P] (q : Evaluation.Port → ℕ) (law : Distribution.ProbDist Z) (f : Z → R)
    {n : ℕ}
    (g : Option Unit × ((Fin n → Z) × ℕ) → (j : (Evaluation Unit R 0).I) →
      (Evaluation Unit R 0).X j → (Option Unit × ((Fin n → Z) × ℕ)) × (Evaluation Unit R 0).Y j)
    (hg : ∀ u t c, g (u, (t, c)) .eval () = ((some (), (t, c + 1)), f (sourceEntry law t c)))
    (hn : q .eval ≤ n) :
    PRG.Lazy.perPort P R (budget := q) •
        Resource.ofAutomaton (Evaluation.perPort Unit R (PRG.Lazy.insideBudget P R q)) g
          ⟨Distribution.fTransform (fun t => (none, (t, 0)))
            (Distribution.pi fun _ : Fin n => law.1),
            Distribution.fTransform_isProbDist _ (Distribution.pi_isProbDist fun _ => law.2)⟩ =
      Resource.sample (Distribution.pi fun _ : P => law.1)
        (fun s => Resource.ofFunction fun _ p => f (s p)) := by
  unfold PRG.Lazy.perPort PRG.Lazy.perPortProgram Converter.ofPreservingProgram
  rw [ofDDC_ofProgramOn_smul_ofAutomaton_pi (A := Evaluation.perPort P R q)
    (B := Evaluation.perPort Unit R (PRG.Lazy.insideBudget P R q)) none (PRG.Lazy.body P R)
    (PRG.Lazy.bound_spec P R)]
  -- The table holds the dictionary: the value of each index is `f` at the entry of its rank.
  refine Resource.ofAutomaton_eq_sample_of_lazyDictionary (A := Evaluation.perPort P R q) (K := P)
    _ law _ (fun _ p => p) (fun _ _ z => f z)
    (fun t st D => st.2.2 = (t, D.length) ∧ ∀ p, (st.1.getD []).lookup p =
      if p ∈ D then some (f (sourceEntry law t (D.idxOf p))) else none)
    (fun t => ⟨rfl, fun p => by simp⟩) ?_ ?_
  · rintro t h ⟨⟨⟩, p⟩ ⟨ls, u, t', c⟩ D hd ⟨hpos, hT⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpos
    rw [PRG.Lazy.combine_eq, hg]
    by_cases hp : p ∈ D
    · rw [hT p, if_pos hp]
      simp only [lazyDictionary, if_pos hp]
      exact ⟨trivial, trivial, hT⟩
    · rw [hT p, if_neg hp]
      simp only [lazyDictionary, if_neg hp, List.idxOf_append_of_notMem hp, List.idxOf_cons_self,
        add_zero, List.length_append, List.length_singleton]
      exact ⟨trivial, trivial, lookup_append_of_dictionary id Function.injective_id
        (f := fun r => f (sourceEntry law _ r)) hT hp⟩
  · intro h hd
    exact (List.toFinset_card_le _).trans ((List.length_map _).trans_le
      ((evaluation_length_le (Or.inr hd)).trans hn))

omit [Nonempty R] in
/-- **`PRG.Lazy` on `prg-real^G` is `G` on a seed per index**: the seed of each index is the
fresh seed of its first query. -/
lemma PRG.Lazy.smul_real (G : S → R) (P : Type) [Fintype P] [DecidableEq P]
    (q : Evaluation.Port → ℕ) :
    PRG.Lazy.perPort P R (budget := q) • PRG.Real.perPort G = PRG.SeedsReal G P := by
  classical
  unfold PRG.Real.perPort Converter.ofProgram PRG.Real.randomness Resource.source
  rw [ofDDC_ofProgramOn_smul_ofAutomaton_pi
    (A := Evaluation.perPort Unit R (PRG.Lazy.insideBudget P R q))
    (B := Interface.source S (PRG.Real.bound G * ∑ i, PRG.Lazy.insideBudget P R q i))
    none (PRG.Real.body G) (PRG.Real.bound_spec G),
    PRG.Lazy.smul_source P q (PRG.Real.law1 G) G _ (PRG.Real.combine_eq G)
      (by simp [PRG.Real.bound, PRG.Lazy.insideBudget])]
  exact Resource.sample_congr_law (P := Distribution.pi fun _ => (PRG.Real.law1 G).1)
    (P' := Distribution.uniform (P → S)) Distribution.pi_uniform _

/-- **`PRG.Lazy` on `prg-rand` is the uniform random function**: the value of each index is the
fresh sample of its first query. -/
lemma PRG.Lazy.smul_rand (P : Type) [Fintype P] [DecidableEq P] (q : Evaluation.Port → ℕ) :
    PRG.Lazy.perPort P R (budget := q) • PRG.Rand.perPort R = URF (Evaluation.perPort P R q) := by
  classical
  unfold PRG.Rand.perPort Converter.ofProgram PRG.Rand.randomness Resource.source
  rw [ofDDC_ofProgramOn_smul_ofAutomaton_pi
    (A := Evaluation.perPort Unit R (PRG.Lazy.insideBudget P R q))
    (B := Interface.source R (PRG.Rand.bound R * ∑ i, PRG.Lazy.insideBudget P R q i))
    none (PRG.Rand.body R) (PRG.Rand.bound_spec R),
    PRG.Lazy.smul_source P q (PRG.Rand.law1 R) id _ PRG.Rand.combine_eq
      (by simp [PRG.Rand.bound, PRG.Lazy.insideBudget]), URF_perPort_eq]
  exact Resource.sample_congr_law (P := Distribution.pi fun _ => (PRG.Rand.law1 R).1)
    (P' := Distribution.uniform (P → R)) Distribution.pi_uniform _

/-- **Many seeds from fresh samples**: if `G` is a secure PRG within `ε` with a fresh seed per
sample, it is a secure many-seed PRG on any indices within `ε` at the distinguishers reduced
through `PRG.Lazy`. -/
lemma prgSeeds_of_prgSamples [Interface.AdmissibleDistinguishers] (G : S → R) (P : Type)
    [Fintype P] [DecidableEq P] {q : Evaluation.Port → ℕ}
    (ε : (Evaluation.perPort Unit R (PRG.Lazy.insideBudget P R q)).inputDomain.DistinguisherBehavior →
      ENNReal)
    (secure : PRG.Samples G ε) :
    PRG.Seeds G P fun D => ε (Interface.absorb (PRG.Lazy.perPort P R) D) := by
  show PRG.SeedsReal G P ≃[_] URF (Evaluation.perPort P R q)
  cc_calc mixed (distinguisherAdvantage AdmissibleDistinguishers.admissible) using
      (fun D _ R S => distinguisherAdvantage_le_distance _ D R S)
    PRG.SeedsReal G P = PRG.Lazy.perPort P R • PRG.Real.perPort G :=
      (PRG.Lazy.smul_real G P q).symm
    _ ≃[ε ∘ absorb (PRG.Lazy.perPort P R)] PRG.Lazy.perPort P R • PRG.Rand.perPort R :=
      AdmissibleDistinguishers.substitutesWithin_context _ secure
    _ = URF (Evaluation.perPort P R q) := PRG.Lazy.smul_rand P q

/-- **`prg-real^G` is indexed by the query number**: the fresh-seed library is `Index` attached
to `G` on a seed per query number. -/
lemma prgReal_eq_index (G : S → R) (q : Evaluation.Port → ℕ) :
    PRG.Real.perPort G (budget := q) =
      Index.perPort R (q .eval) • PRG.SeedsReal G (Fin (q .eval)) := by
  classical
  rw [PRG.Real.perPort, PRG.Real.randomness, Resource.source, Converter.ofProgram_smul_ofAutomaton]
  erw [Resource.ofAutomaton_fTransform]
  erw [Resource.sample_fTransform]
  rw [PRG.SeedsReal, Resource.smul_sample]
  have index : ∀ s : Fin (q .eval) → S, Index.perPort R (q .eval) (budget := q) •
      Resource.ofFunction (A := Evaluation.perPort (Fin (q .eval)) R
        (Index.insideBudget R (q .eval) q)) (fun _ p => G (s p)) =
      Resource.ofAutomaton (Evaluation.perPort Unit R q)
        ((Index.body R (q .eval)).combine (fun (_ : Unit) _ k => ((), G (s k)))
          (Index.bound_spec R _)) (Distribution.ProbDist.single (none, ())) :=
    fun s => Index.smul_ofFunction (q .eval) q (fun p => G (s p))
  simp only [index]
  have hn : PRG.Real.bound G * ∑ i, q i = q .eval := by simp [PRG.Real.bound]
  rw [Resource.sample_congr_law (P := Distribution.pi fun _ => (PRG.Real.law1 G).1)
    (P' := Distribution.uniform (Fin (PRG.Real.bound G * ∑ i, q i) → S)) Distribution.pi_uniform]
  conv_lhs => rw [Resource.sample_uniform_equiv ((finCongr hn.symm).arrowCongr (Equiv.refl S))]
  congr 1
  funext s
  -- The `c`-th fresh seed is the entry `c` of the table, and `Index` reads entry `c` of `s`.
  refine Resource.ofAutomaton_single_congr_on_domain (fun h
    (sL : Option Unit × ((Fin (PRG.Real.bound G * ∑ i, q i) → S) × ℕ)) (sR : Option ℕ × Unit) =>
    sL.2.1 = ((finCongr hn.symm).arrowCongr (Equiv.refl S)) s ∧ sL.2.2 = h.length ∧
      (sR.1.getD 0 : ℕ) = h.length) ⟨rfl, rfl, rfl⟩ ?_
  rintro h ⟨⟨⟩, ⟨⟩⟩ ⟨stL, tL, c⟩ ⟨(stR : Option ℕ), ⟨⟩⟩ hd ⟨rfl, rfl, hR⟩
  have hq : h.length < q .eval := by
    simpa using evaluation_length_le (X := Unit) (Y := R) (Or.inr hd)
  have hq' : h.length < PRG.Real.bound G * ∑ i, q i := by rw [hn]; exact hq
  have entry : sourceEntry (PRG.Real.law1 G)
      (((finCongr hn.symm).arrowCongr (Equiv.refl S)) s) h.length = s ⟨h.length, hq⟩ := by
    simp only [sourceEntry, sourceStep]
    rw [dif_pos hq']
    rfl
  rw [PRG.Real.combine_eq, Index.combine_eq (q .eval) (fun k => G (s k))]
  dsimp only at hR ⊢
  simp only [hR, dif_pos hq]
  exact ⟨congrArg G entry, by simp⟩


/-- **`prg-rand` is indexed by the query number**: the fresh uniform samples are `Index` attached
to the uniform random function on the query numbers. -/
lemma prgRand_eq_index (q : Evaluation.Port → ℕ) :
    PRG.Rand.perPort R (budget := q) =
      Index.perPort R (q .eval) • URF (Evaluation.perPort (Fin (q .eval)) R
        (Index.insideBudget R (q .eval) q)) := by
  classical
  rw [PRG.Rand.perPort, PRG.Rand.randomness, Resource.source, Converter.ofProgram_smul_ofAutomaton]
  erw [Resource.ofAutomaton_fTransform]
  erw [Resource.sample_fTransform]
  rw [URF_perPort_eq, Resource.smul_sample]
  have index : ∀ g : Fin (q .eval) → R, Index.perPort R (q .eval) (budget := q) •
      Resource.ofFunction (A := Evaluation.perPort (Fin (q .eval)) R
        (Index.insideBudget R (q .eval) q)) (fun _ => g) =
      Resource.ofAutomaton (Evaluation.perPort Unit R q)
        ((Index.body R (q .eval)).combine (fun (_ : Unit) _ k => ((), g k))
          (Index.bound_spec R _)) (Distribution.ProbDist.single (none, ())) :=
    fun g => Index.smul_ofFunction (q .eval) q g
  simp only [index]
  have hn : PRG.Rand.bound R * ∑ i, q i = q .eval := by simp [PRG.Rand.bound]
  rw [Resource.sample_congr_law (P := Distribution.pi fun _ => (PRG.Rand.law1 R).1)
    (P' := Distribution.uniform (Fin (PRG.Rand.bound R * ∑ i, q i) → R)) Distribution.pi_uniform]
  conv_lhs => rw [Resource.sample_uniform_equiv ((finCongr hn.symm).arrowCongr (Equiv.refl R))]
  congr 1
  funext g
  -- The `c`-th fresh sample is the entry `c` of the table, and `Index` reads entry `c` of `g`.
  refine Resource.ofAutomaton_single_congr_on_domain (fun h
    (sL : Option Unit × ((Fin (PRG.Rand.bound R * ∑ i, q i) → R) × ℕ)) (sR : Option ℕ × Unit) =>
    sL.2.1 = ((finCongr hn.symm).arrowCongr (Equiv.refl R)) g ∧ sL.2.2 = h.length ∧
      (sR.1.getD 0 : ℕ) = h.length) ⟨rfl, rfl, rfl⟩ ?_
  rintro h ⟨⟨⟩, ⟨⟩⟩ ⟨stL, tL, c⟩ ⟨(stR : Option ℕ), ⟨⟩⟩ hd ⟨rfl, rfl, hR⟩
  have hq : h.length < q .eval := by
    simpa using evaluation_length_le (X := Unit) (Y := R) (Or.inr hd)
  have hq' : h.length < PRG.Rand.bound R * ∑ i, q i := by rw [hn]; exact hq
  have entry : sourceEntry (PRG.Rand.law1 R)
      (((finCongr hn.symm).arrowCongr (Equiv.refl R)) g) h.length = g ⟨h.length, hq⟩ := by
    simp only [sourceEntry, sourceStep]
    rw [dif_pos hq']
    rfl
  rw [PRG.Rand.combine_eq, Index.combine_eq (q .eval) g]
  dsimp only at hR ⊢
  simp only [hR, dif_pos hq]
  exact ⟨entry, by simp⟩

end Seeds

section Ordering

open SystemAlgebra.Interface

variable (X : Type) [Fintype X] [DecidableEq X] [Nonempty X]

/-- **Samples without replacement, indexed**: a uniformly random ordering of `X`, sampled once,
and the index `k` answered with its `k`-th value. -/
def orderedSamples (n : ℕ) {q : Evaluation.Port → ℕ} :
    Resource (Evaluation.perPort (Fin n) X q) :=
  Resource.sample (Distribution.uniform (Equiv.Perm X)) fun ordering =>
    Resource.ofFunction fun _ k =>
      ordering ((Fintype.equivFin X).symm (Fin.ofNat (Fintype.card X) k.val))

/-- `samp-uniq` against its source: the first query reads the ordering. -/
lemma SampUniq.combine_first {k : ℕ} (t : Fin k → Equiv.Perm X) (c : ℕ) :
    (SampUniq.body X).combine (sourceStep (q := k) (SampUniq.law1 X)) (SampUniq.bound_spec X)
        (none, (t, c)) .eval () =
      ((some (sourceEntry (SampUniq.law1 X) t c, 1), (t, c + 1)),
        sourceEntry (SampUniq.law1 X) t c ((Fintype.equivFin X).symm (Fin.ofNat _ 0))) :=
  Program.combine_eq_of_invoke _ _ (n := 1) (by
    simp [Program.invoke, SampUniq.body, callProg, returnProg, sourceStep, sourceEntry])

/-- `samp-uniq` once the ordering is stored. -/
lemma SampUniq.combine_later {k : ℕ} (σ : Equiv.Perm X) (n : ℕ)
    (r : (Fin k → Equiv.Perm X) × ℕ) :
    (SampUniq.body X).combine (sourceStep (q := k) (SampUniq.law1 X)) (SampUniq.bound_spec X)
        (some (σ, n), r) .eval () =
      ((some (σ, n + 1), r), σ ((Fintype.equivFin X).symm (Fin.ofNat _ n))) :=
  Program.combine_eq_of_invoke _ _ (n := 0) (by
    simp [Program.invoke, SampUniq.body, returnProg])

/-- **`samp-uniq` is indexed by the query number**: it is `Index` attached to `orderedSamples`. -/
lemma sampUniq_eq_index (q : Evaluation.Port → ℕ) :
    SampUniq.perPort X (budget := q) = Index.perPort X (q .eval) • orderedSamples X (q .eval) := by
  classical
  rw [SampUniq.perPort, SampUniq.randomness, Resource.source, Converter.ofProgram_smul_ofAutomaton]
  erw [Resource.ofAutomaton_fTransform]
  erw [Resource.sample_fTransform]
  rw [orderedSamples, Resource.smul_sample]
  -- The ordering is the first entry of the table; the `c`-th sample is its `c`-th value.
  let index : Equiv.Perm X → Resource (Evaluation.perPort Unit X q) := fun σ =>
    Resource.ofAutomaton (Evaluation.perPort Unit X q)
      ((Index.body X (q .eval)).combine (fun (_ : Unit) _ k =>
        ((), σ ((Fintype.equivFin X).symm (Fin.ofNat (Fintype.card X) k.val))))
        (Index.bound_spec X _)) (Distribution.ProbDist.single (none, ()))
  have hR : ∀ σ : Equiv.Perm X, Index.perPort X (q .eval) (budget := q) •
      Resource.ofFunction (A := Evaluation.perPort (Fin (q .eval)) X
        (Index.insideBudget X (q .eval) q))
        (fun _ k => σ ((Fintype.equivFin X).symm (Fin.ofNat (Fintype.card X) k.val))) = index σ :=
    fun σ => Index.smul_ofFunction (q .eval) q
      (fun k => σ ((Fintype.equivFin X).symm (Fin.ofNat (Fintype.card X) k.val)))
  have hL : ∀ t : Fin (SampUniq.bound X * ∑ i, q i) → Equiv.Perm X,
      Resource.ofAutomaton (Evaluation.perPort Unit X q)
        ((SampUniq.body X).combine (sourceStep (SampUniq.law1 X)) (SampUniq.bound_spec X))
        (Distribution.ProbDist.single (none, (t, 0))) =
      index (sourceEntry (SampUniq.law1 X) t 0) := by
    intro t
    refine Resource.ofAutomaton_single_congr_on_domain (fun h
      (sL : Option (Equiv.Perm X × ℕ) × ((Fin (SampUniq.bound X * ∑ i, q i) → Equiv.Perm X) × ℕ))
      (sR : Option ℕ × Unit) =>
        (h = [] ∧ sL = (none, (t, 0)) ∨
          h ≠ [] ∧ sL.1 = some (sourceEntry (SampUniq.law1 X) t 0, h.length)) ∧
          (sR.1.getD 0 : ℕ) = h.length) ⟨Or.inl ⟨rfl, rfl⟩, rfl⟩ ?_
    rintro h ⟨⟨⟩, ⟨⟩⟩ ⟨stL, r⟩ ⟨(stR : Option ℕ), ⟨⟩⟩ hd ⟨hL, hR⟩
    have hq : h.length < q .eval := by
      simpa using evaluation_length_le (X := Unit) (Y := X) (Or.inr hd)
    rw [Index.combine_eq (q .eval) (fun k => sourceEntry (SampUniq.law1 X) t 0
      ((Fintype.equivFin X).symm (Fin.ofNat (Fintype.card X) k.val)))]
    dsimp only at hR hL ⊢
    simp only [hR, dif_pos hq]
    rcases hL with ⟨rfl, hL⟩ | ⟨hne, hL⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hL
      rw [SampUniq.combine_first]
      exact ⟨rfl, by simp⟩
    · subst hL
      rw [SampUniq.combine_later]
      exact ⟨rfl, by simp⟩
  simp only [hR, hL]
  rw [← Resource.sample_fTransform (fun t => sourceEntry (SampUniq.law1 X) t 0) _ index]
  by_cases hk : 0 < SampUniq.bound X * ∑ i, q i
  · exact Resource.sample_congr_law (sourceEntry_zero_law _ hk) _
  · exact Resource.eq_of_not_domain fun h hd => hk
      (Nat.mul_pos (by norm_num [SampUniq.bound]) (bound_pos_of_domain hd))


omit [Fintype X] [DecidableEq X] [Nonempty X] in
/-- Two queried indices get the same value. -/
def Repeated {X : Type} {n : ℕ} (y : Fin n → X) (ks : List (Fin n)) : Prop :=
  ∃ k ∈ ks, ∃ k' ∈ ks, k ≠ k' ∧ y k = y k'

omit [Fintype X] [DecidableEq X] [Nonempty X] in
lemma repeated_monotone {X : Type} {n : ℕ} (y : Fin n → X) {ks ks' : List (Fin n)}
    (hp : ks <+: ks') : Repeated y ks → Repeated y ks' :=
  fun ⟨k, hk, k', hk', distinct, equal⟩ => ⟨k, hp.subset hk, k', hp.subset hk', distinct, equal⟩

/-- **The birthday game**: a uniform function on the indices, with the hidden condition that two
queried indices get the same value. -/
def birthdayGame (n : ℕ) (q : Evaluation.Port → ℕ) :=
  PDG.ofSingleFunction (Evaluation.perPort (Fin n) X q).domain
    (Evaluation.perPort (Fin n) X q).nonempty_prefix (Evaluation.perPort (Fin n) X q).bound
    (Evaluation.perPort (Fin n) X q).length_le (Distribution.uniform (Fin n → X)) (fun y k => y k)
    (fun y => ⟨Repeated y, fun {_ _} hp => repeated_monotone y hp⟩)

/-- Without a repeated value, the values of a uniform function at distinct indices have the law
of samples without replacement. -/
lemma birthday_game_equiv (n : ℕ) (q : Evaluation.Port → ℕ) (hn : n ≤ Fintype.card X) :
    birthdayGame X n q |≡ orderedSamples X n (q := q) := by
  classical
  -- The ordering's values at the indices: a uniform injection, by transitivity of the
  -- permutations on injections.
  let e : Fin n → X := fun k => (Fintype.equivFin X).symm (Fin.ofNat (Fintype.card X) k.val)
  have he : Function.Injective e := by
    intro k k' h
    have := congrArg Fin.val ((Fintype.equivFin X).symm.injective h)
    simp only [Fin.val_ofNat] at this
    rw [Nat.mod_eq_of_lt (k.isLt.trans_le hn), Nat.mod_eq_of_lt (k'.isLt.trans_le hn)] at this
    exact Fin.ext this
  have ordered : orderedSamples X n (q := q) = Interface.Resource.sample
      (Distribution.fTransform (fun σ : Equiv.Perm X => fun k => σ (e k))
        (Distribution.uniform _)) (fun g => Interface.Resource.ofFunction fun _ => g) := by
    unfold orderedSamples
    exact (Interface.Resource.sample_fTransform (fun σ : Equiv.Perm X => fun k => σ (e k))
      (Distribution.uniform _)
      (fun g => Interface.Resource.ofFunction (A := Evaluation.perPort (Fin n) X q)
        fun _ => g)).symm
  rw [ordered]
  apply PDG.ofSingleFunction_gameEquivalent
  intro ks a
  rw [Distribution.mass_fTransform]
  dsimp only
  let S := ks.toFinset
  by_cases hinj : Set.InjOn a S
  · let b : S ↪ X := ⟨fun i => a i.1, fun i j h => Subtype.ext (hinj i.2 j.2 h)⟩
    let p : S ↪ X := ⟨fun i => e i.1, fun i j h => Subtype.ext (he h)⟩
    have hQ : (Distribution.uniform (Equiv.Perm X)).mass (fun σ => ∀ k ∈ ks, σ (e k) = a k) =
        1 / Fintype.card (S ↪ X) := by
      rw [← Counting.uniform_perm_mass_eq_inv p b]
      exact Distribution.mass_congr _ fun σ => ⟨fun h i => h i.1 (List.mem_toFinset.mp i.2),
        fun h k hk => h ⟨k, List.mem_toFinset.mpr hk⟩⟩
    have hL : (Distribution.uniform (Fin n → X)).mass
        (fun y => (∀ k ∈ ks, y k = a k) ∧ ¬ Repeated y ks) =
          (1 / (Fintype.card X : ℝ)) ^ S.card := by
      rw [← Counting.uniform_mass_apply_list_eq ks id (Set.injOn_id _) a]
      refine Distribution.mass_congr _ fun y => ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      have h' : ∀ x ∈ ks, y x = a x := h
      rintro ⟨k, hk, k', hk', hne, heq⟩
      rw [h' k hk, h' k' hk'] at heq
      exact hne (hinj (List.mem_toFinset.mpr hk) (List.mem_toFinset.mpr hk') heq)
    have hP : (Distribution.uniform (Fin n → X)).mass (fun y => ¬ Repeated y ks) =
        Fintype.card (S ↪ X) * (1 / (Fintype.card X : ℝ)) ^ S.card := by
      rw [Distribution.mass_eq_sum_mass_fiber _ _ (fun y : Fin n → X =>
        if h : Function.Injective (fun i : S => y i.1) then (⟨_, h⟩ : S ↪ X) else b)
        Finset.univ (fun _ _ => Finset.mem_univ _)]
      have each : ∀ v : S ↪ X, (Distribution.uniform (Fin n → X)).mass (fun y =>
          ¬ Repeated y ks ∧ (if h : Function.Injective (fun i : S => y i.1) then
            (⟨_, h⟩ : S ↪ X) else b) = v) = (1 / (Fintype.card X : ℝ)) ^ S.card := by
        intro v
        rw [← Fintype.card_coe S, ← Counting.uniform_mass_eval_eq (X := Fin n) (Y := X)
          (fun i : S => i.1) Subtype.val_injective (fun i => v i)]
        refine Distribution.mass_congr _ fun y => ?_
        have rep : ¬ Repeated y ks ↔ Function.Injective (fun i : S => y i.1) := by
          constructor
          · intro h i j hij
            by_contra hne
            exact h ⟨i.1, List.mem_toFinset.mp i.2, j.1, List.mem_toFinset.mp j.2,
              fun he => hne (Subtype.ext he), hij⟩
          · rintro h ⟨k, hk, k', hk', hne, heq⟩
            exact hne (congrArg Subtype.val (h (a₁ := ⟨k, List.mem_toFinset.mpr hk⟩)
              (a₂ := ⟨k', List.mem_toFinset.mpr hk'⟩) heq))
        rw [rep]
        constructor
        · rintro ⟨h, hv⟩
          rw [dif_pos h] at hv
          funext i
          exact congrArg (fun f : S ↪ X => f i) hv
        · intro hv
          have h : Function.Injective (fun i : S => y i.1) := by
            intro i j hij
            exact v.injective (by simpa [← congrFun hv i, ← congrFun hv j] using hij)
          refine ⟨h, ?_⟩
          rw [dif_pos h]
          exact Function.Embedding.ext fun i => congrFun hv i
      simp only [each, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (0 : ℝ) < Fintype.card (S ↪ X) := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨b⟩
    rw [hL, hQ, hP]
    field_simp
  · -- The prescribed values repeat, which neither the game without repetition nor the ordering
    -- can give.
    have hS : ∃ k ∈ ks, ∃ k' ∈ ks, k ≠ k' ∧ a k = a k' := by
      simp only [Set.InjOn, not_forall] at hinj
      obtain ⟨k, hk, k', hk', heq, hne⟩ := hinj
      exact ⟨k, List.mem_toFinset.mp hk, k', List.mem_toFinset.mp hk', hne, heq⟩
    obtain ⟨k, hk, k', hk', hne, heq⟩ := hS
    rw [Distribution.mass_eq_zero_of_forall_not _ fun y h => h.2 ⟨k, hk, k', hk', hne,
        by rw [h.1 k hk, h.1 k' hk', heq]⟩,
      Distribution.mass_eq_zero_of_forall_not _ fun σ h => hne (he (σ.injective
        (by rw [h k hk, h k' hk', heq]))), zero_mul]

/-- Blind winning is a repetition among at most `q` fixed indices. -/
lemma birthdayGame_blind_bound (n : ℕ) (q : Evaluation.Port → ℕ) :
    ν((birthdayGame X n q).blind (Evaluation.perPort (Fin n) X q).nonempty_prefix) ≤
      (q .eval : ℝ) * ((q .eval : ℝ) - 1) / (2 * Fintype.card X) := by
  have hq : 0 ≤ (q .eval : ℝ) * ((q .eval : ℝ) - 1) := by
    simpa using natCast_mul_sub_one_le (Nat.zero_le (q .eval)) le_rfl
  apply PDG.ofFunction_blind_le (div_nonneg hq (by positivity))
  intro xs hxs
  let S := (xs.map Sigma.snd).toFinset
  have hS : S.card ≤ q .eval :=
    (List.toFinset_card_le _).trans ((List.length_map _).trans_le (evaluation_length_le hxs))
  change (Distribution.uniform (Fin n → X)).mass (fun y => Repeated y (xs.map Sigma.snd)) ≤ _
  -- A union bound over the pairs of distinct queried indices.
  calc _ = (Distribution.uniform (Fin n → X)).mass
        (fun y => ∃ k ∈ S, ∃ k' ∈ S, k ≠ k' ∧ y k = y k') :=
        Distribution.mass_congr _ fun y => by simp [Repeated, S]
    _ ≤ S.card * (S.card - 1) / 2 * (1 / Fintype.card X) :=
        Distribution.mass_exists_pair_le Distribution.uniform_nonNeg S _
          (fun _ _ _ h => h.symm) fun _ _ _ _ h => Counting.uniform_mass_apply_eq_le h
    _ ≤ _ := by
        rw [div_mul_div_comm, mul_one]
        exact div_le_div_of_nonneg_right (by simpa using natCast_mul_sub_one_le hS le_rfl)
          (by positivity)

/-- **The birthday lemma, indexed**: the uniform random function on the indices is within
`q(q-1)/(2|X|)` of samples without replacement. -/
lemma urf_orderedSamples_distance_le (n : ℕ) (q : Evaluation.Port → ℕ)
    (hn : n ≤ Fintype.card X) :
    Δ (URF (Evaluation.perPort (Fin n) X q)) (orderedSamples X n (q := q)) ≤
      ENNReal.ofReal ((q .eval : ℝ) * ((q .eval : ℝ) - 1) / (2 * Fintype.card X)) :=
  ((birthday_game_equiv X n q hn).game_dist_ofSingleFunction_le (URF_perPort_eq _ _)).trans
    (ENNReal.ofReal_le_ofReal (birthdayGame_blind_bound X n q))

omit [DecidableEq X] in
/-- **Past `|X|` samples the birthday bound is trivial**: for `q > |X|`, `q(q-1)/(2|X|)` is at
least `1`, which bounds every distance. -/
lemma distance_le_birthday_of_card_lt {A : Interface} (R S : Interface.Resource A) {q : ℕ}
    (hq : Fintype.card X < q) :
    Δ R S ≤ ENNReal.ofReal ((q : ℝ) * ((q : ℝ) - 1) / (2 * Fintype.card X)) := by
  -- The distance of two resources is the transcript distance of their random systems, at most 1.
  refine ((Interface.cc_distance_eq _ _).trans_le
    (RandomSystem.transcriptDistance_le_one R.2 S.2)).trans ?_
  -- It remains `1 ≤ q(q-1)/(2|X|)`, i.e. `2|X| ≤ q(q-1)`: from `|X| ≥ 1` and `q ≥ |X| + 1`.
  rw [ENNReal.one_le_ofReal]
  have hX : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hq' : (Fintype.card X : ℝ) + 1 ≤ q := by exact_mod_cast hq
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **The birthday lemma** [1, §2]: `q` fresh uniform samples are within `q(q-1)/(2|X|)` of `q`
samples without replacement. -/
theorem prgRand_sampUniq_distance_le (q : Evaluation.Port → ℕ) :
    Δ (PRG.Rand.perPort X (budget := q)) (SampUniq.perPort X (budget := q)) ≤
      ENNReal.ofReal ((q .eval : ℝ) * ((q .eval : ℝ) - 1) / (2 * Fintype.card X)) := by
  -- Indexed by the query number, the two systems are `Index` on the uniform random function and
  -- on samples without replacement, until `|X|` samples; past them the bound is at least `1`.
  by_cases hq : q .eval ≤ Fintype.card X
  · rw [prgRand_eq_index, sampUniq_eq_index]
    exact (Interface.distance_smul_le _ _ _).trans
      (urf_orderedSamples_distance_le X (q .eval) _ hq)
  · exact distance_le_birthday_of_card_lt X _ _ (not_le.mp hq)

end Ordering

end

end Commons
