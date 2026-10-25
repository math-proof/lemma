import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCompactHolderObstruction
open StatMech StatMech.Universality


/--
[meshScaleLinearField_local_norm_sub_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCompactHolderObstruction.lean)
-/
@[path]
private lemma meshScaleLinearField_local_norm_sub_sq_le_eq
  {k : Nat}
  {z w : Complex}
-- given
  (hzw : dist z w ≤ 1 / (k + 1 : Real)) :
-- imply
  ‖meshScaleLinearField k z - meshScaleLinearField k w‖ ^ 2 ≤ dist z w := by
-- proof
  apply StatMech.Universality.meshScaleLinearField_local_norm_sub_sq_le k z w hzw

/--
[meshScaleLinearField_not_meshUniformCompactHolder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCompactHolderObstruction.lean)
-/
@[path]
private lemma meshScaleLinearField_not_meshUniformCompactHolder_eq :
-- imply
  ¬ Nonempty (fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder meshScaleLinearField) := by
-- proof
  apply StatMech.Universality.meshScaleLinearField_not_meshUniformCompactHolder


-- created on 2026-10-23
