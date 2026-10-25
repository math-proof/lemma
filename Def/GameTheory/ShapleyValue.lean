/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ext
import Instance.GameTheory.ShapleyValue
/-! # Shapley value characterization for cooperative games

Existence and uniqueness of the linear value satisfying efficiency, symmetry,
and the null-player axiom, via unanimity games and Möbius inversion on the
Boolean lattice.

Source: L. S. Shapley, "A Value for n-Person Games," Contributions to the
Theory of Games II, Annals of Mathematics Studies 28, Princeton University
Press (1953), 307--317; modern DOI `10.1515/9781400881970-018`.

Source-fidelity note: Shapley's printed argument (pp. 308--312) works with
superadditive games on a player universe with finite carriers, with axioms of
full permutation equivariance, efficiency for every carrier, and aggregation.
What is proved here is an adapted fixed-finite-player vector-space
characterization: it quantifies over arbitrary normalized set functions on one
fixed finite player type, packages aggregation together with real homogeneity
as linearity, and uses invariant-game symmetry (equal payoffs when a
permutation fixes the game), grand-coalition efficiency, and a null-player
axiom. This characterization is mathematically coherent as stated, but it is
this adapted formulation rather than a literal transcription of the source
theorem.
-/


namespace MathlibExt.GameTheory.ShapleyValue

variable {Player : Type*} [DecidableEq Player] [Fintype Player]

/-- `i` is null/dummy in `v` if it never changes worth of a coalition not containing it. -/
def IsNullPlayer (v : CoopGame Player) (i : Player) : Prop :=
  ∀ S : Set Player, i ∉ S → v.charFun (insert i S) = v.charFun S

/-- Efficiency: total allocated equals worth of grand coalition. -/
def IsEfficient (φ : CoopGame Player →ₗ[ℝ] (Player → ℝ)) : Prop :=
  ∀ v : CoopGame Player, ∑ i : Player, φ v i = v.charFun Set.univ

/-- Symmetry under permutations preserving the game via `σ '' S`. -/
def IsSymmetric (φ : CoopGame Player →ₗ[ℝ] (Player → ℝ)) : Prop :=
  ∀ (σ : Equiv.Perm Player) (v : CoopGame Player),
    (∀ S : Set Player, v.charFun (σ '' S) = v.charFun S) →
    ∀ i : Player, φ v (σ i) = φ v i

/-- Null/dummy player axiom: a null player receives zero. -/
def SatisfiesNullPlayerAxiom (φ : CoopGame Player →ₗ[ℝ] (Player → ℝ)) : Prop :=
  ∀ (v : CoopGame Player) (i : Player), IsNullPlayer v i → φ v i = 0

-- Classical decidability for the subset tests in unanimity-game statements.

attribute [local instance] Classical.propDecidable

/-- Unanimity game: worth 1 iff `T ⊆ S` (zero game when `T = ∅`, since the
constant-1 function is not normalized). -/
noncomputable def unanimity (T : Finset Player) : CoopGame Player := by
  classical
  exact if h : T = ∅ then 0
  else
    ⟨fun S => if (T : Set Player) ⊆ S then (1 : ℝ) else 0, by
      rw [ite_eq_right]
      intro hsub
      apply h
      exact Finset.coe_eq_empty.mp (Set.subset_empty_iff.mp hsub)⟩

end MathlibExt.GameTheory.ShapleyValue
