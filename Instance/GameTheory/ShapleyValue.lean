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
import Structure.GameTheory.ShapleyValue
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

namespace CoopGame

variable {Player : Type*}

instance : AddCommGroup (CoopGame Player) where
  add v w :=
    ⟨fun S => v.charFun S + w.charFun S, by simp [v.empty, w.empty]⟩
  add_assoc a b c := by
    ext S
    exact add_assoc (a.charFun S) (b.charFun S) (c.charFun S)
  zero := ⟨fun _ => 0, rfl⟩
  zero_add a := by
    ext S
    exact zero_add (a.charFun S)
  add_zero a := by
    ext S
    exact add_zero (a.charFun S)
  nsmul n v :=
    ⟨fun S => n • v.charFun S, by simp [v.empty]⟩
  neg v :=
    ⟨fun S => -v.charFun S, by simp [v.empty]⟩
  zsmul n v :=
    ⟨fun S => n • v.charFun S, by simp [v.empty]⟩
  neg_add_cancel a := by
    ext S
    exact neg_add_cancel (a.charFun S)
  add_comm a b := by
    ext S
    exact add_comm (a.charFun S) (b.charFun S)

instance : SMul ℝ (CoopGame Player) where
  smul c v := ⟨fun S => c * v.charFun S, by simp [v.empty]⟩

instance : Module ℝ (CoopGame Player) where
  one_smul v := by
    ext S
    exact one_mul (v.charFun S)
  mul_smul c₁ c₂ v := by
    ext S
    exact mul_assoc c₁ c₂ (v.charFun S)
  smul_zero c := by
    ext S
    exact mul_zero c
  smul_add c v w := by
    ext S
    exact mul_add c (v.charFun S) (w.charFun S)
  add_smul c₁ c₂ v := by
    ext S
    exact add_mul c₁ c₂ (v.charFun S)
  zero_smul v := by
    ext S
    exact zero_mul (v.charFun S)

end CoopGame
end MathlibExt.GameTheory.ShapleyValue
