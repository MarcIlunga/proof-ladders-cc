import ConstructiveCryptography.InterfaceGame
import RandomSystems.Game.DiscreteMBO

/-!
# Games of winning conditions

A resource with a winning condition on its transcripts is a game: the resource, with the MBO
set once the transcript satisfies the condition. This is the shape of a game whose flag `win` is
set by an oracle call, as in the multi-user games of the protocol ladder: the condition holds on
a transcript whose last query sets `win`. The game is the behavior of the discrete game of a
presentation of the resource, whose condition on each deterministic system is that the winning
condition held on the transcript of some answered prefix of the queries; its visible resource is
the resource.

In every compatible solver class, a lossy reduction carries over to a game with a converter
attached: the converter is absorbed into the solver (`win_attach_le_of_reduction`).

Upstream candidates: `CompatibleSolverClass.win_attach_le_of_reduction`, for
`ConstructiveCryptography.CryptographicAlgebra.Game`; `Interface.Transcript`,
`Interface.Game.condition` and `Interface.Game.ofWins` with `Interface.Game.visible_ofWins`, for
`ConstructiveCryptography.InterfaceGame`.

## Main definitions

* `Interface.Transcript A`: the transcripts of `A`
* `Interface.Game.ofWins R wins`: the game of a resource with a winning condition

## Main results

* `CompatibleSolverClass.win_attach_le_of_reduction`: a lossy reduction through a converter
* `Interface.Game.visible_ofWins`: its visible resource is the resource
-/

namespace SystemAlgebra.Interface

open Classical Probability ConstructiveCryptography

/-- The transcripts of `A`: its queries with their replies. -/
abbrev Transcript (A : Interface) := List ((Σ i, A.X i) × Σ i, A.Y i)

namespace Game

variable {A : Interface}

/-- The condition of a deterministic system with a winning condition: the winning condition
held on the transcript of some answered prefix of the queries. -/
def condition (s : InterfaceSystem A.I A.X A.Y) (wins : A.Transcript → Prop) :
    MC (Σ i, A.X i) :=
  ⟨fun xs => ∃ p, p <+: xs ∧ ∃ ys, Replies s p ys ∧ wins (p.zip ys),
    fun {_ _} hk ⟨p, hp, hw⟩ => ⟨p, hp.trans hk, hw⟩⟩

/-- The discrete game of a resource with a winning condition, on a presentation of the
resource. -/
noncomputable def presentation (R : Resource A) (wins : A.Transcript → Prop) :
    PDG (Σ i, A.X i) (Σ i, A.Y i) A.inputDomain :=
  Distribution.fTransform (fun s => ⟨(⟨s.1, s.2.1⟩, condition s.1 wins),
    HasDomain.ofInputs s.2.2.2⟩) (Classical.choose R.exists_ofPDS).1

lemma presentation_isProbDist (R : Resource A) (wins : A.Transcript → Prop) :
    (presentation R wins).isProbDist :=
  Distribution.fTransform_isProbDist _ (Classical.choose R.exists_ofPDS).2

/-- The visible systems of the presentation are the resource. -/
lemma behavior_underlying_presentation (R : Resource A) (wins : A.Transcript → Prop) :
    PDS.behavior (presentation R wins).underlying
      (PDG.underlying_probability (presentation_isProbDist R wins)) = R.1 := by
  have hQ := Classical.choose_spec R.exists_ofPDS
  conv_rhs => rw [← hQ]
  apply RandomSystem.ext
  intro h
  rw [PDS.behavior_mass, behaviorMass, PDG.underlying, Distribution.mass_fTransform, presentation,
    Distribution.mass_fTransform]
  rfl

/-- **The game of a resource with a winning condition**: the resource, with the MBO set once the
transcript satisfies the winning condition. -/
noncomputable def ofWins (R : Resource A) (wins : A.Transcript → Prop) : Game A :=
  ⟨⟨(presentation R wins).behavior (presentation_isProbDist R wins),
      PDG.repliesAtQueriedInterface_behavior (presentation_isProbDist R wins)
        ((behavior_underlying_presentation R wins).symm ▸ R.2)⟩,
    PDG.monotoneMBO_behavior (presentation_isProbDist R wins)⟩

/-- The visible resource of the game of a resource with a winning condition is the resource. -/
lemma visible_ofWins (R : Resource A) (wins : A.Transcript → Prop) :
    GameTheory.visible (ofWins R wins) = R := by
  apply Subtype.ext
  change ((presentation R wins).behavior (presentation_isProbDist R wins)).visible = R.1
  exact (PDG.visible_behavior _).trans (behavior_underlying_presentation R wins)

end Game

end SystemAlgebra.Interface

namespace ConstructiveCryptography.CompatibleSolverClass

open CategoryTheory GameTheory

universe u v w x

variable {C : Type u} [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]
  {Game : C → Type x} [GameTheory C Phi Game] [CompatibleSolverClass C Phi Game]

/-- **A lossy reduction through a converter**: if every solver wins `G₁` with at most `k` times
its probability of winning `α • G₂`, then every solver wins `β • G₁` with at most `k` times its
probability of winning `(β ≫ α) • G₂`. The converter `β` is absorbed into the solver. -/
lemma win_attach_le_of_reduction {A B D : C} (β : A ⟶ B) (α : B ⟶ D) {G₁ : Game B}
    {G₂ : Game D} {k : ℝ} (reduction : ∀ s ∈ solvers B, s.2 G₁ ≤ k * s.2 (α • G₂))
    {s : (Phi A → ℝ) × (Game A → ℝ)} (hs : s ∈ solvers A) :
    s.2 (β • G₁) ≤ k * s.2 ((β ≫ α) • G₂) := by
  simp only [smul_eq_attachGame, attachGame_serial]
  exact reduction _ (absorb_mem β hs)

end ConstructiveCryptography.CompatibleSolverClass
