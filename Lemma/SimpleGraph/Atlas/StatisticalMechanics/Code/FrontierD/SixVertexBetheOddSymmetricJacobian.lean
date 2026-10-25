import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricJacobian
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexOddSymmetricBetheRootJacobian_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricJacobian.lean)
-/
@[path]
private lemma sixVertexOddSymmetricBetheRootJacobian_apply_eq
  {N m : Nat}
  {c : Real}
  {q v : Fin m → Real}
  {j : Fin m}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexOddSymmetricBetheRootJacobian N m c q v j = sixVertexBetheRootJacobian N ((m + 1) + m) c (sixVertexOddSymmetricLift m q) (sixVertexOddSymmetricLift m v) (sixVertexOddPositiveIndex m j) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricBetheRootJacobian_apply hc q v j

/--
[sixVertexOddSymmetricBetheRootJacobian_toMatrix'_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricJacobian.lean)
-/
@[path]
private lemma sixVertexOddSymmetricBetheRootJacobian_toMatrix'_apply_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
  {j k : Fin m}
-- given
  (hc : 2 < c) :
-- imply
  LinearMap.toMatrix' (sixVertexOddSymmetricBetheRootJacobian N m c q).toLinearMap j k = sixVertexBetheOddPositiveHalfJacobianMatrix N m c q j k := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricBetheRootJacobian_toMatrix'_apply hc q j k

/--
[sixVertexOddSymmetricBetheRootJacobian_injective_of_diagonalDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricJacobian.lean)
-/
@[path]
private lemma sixVertexOddSymmetricBetheRootJacobian_injective_of_diagonalDominance_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
-- given
  (hc : 2 < c)
  (hdom : ∀ j, ∑ k ∈ Finset.univ.erase j, ‖sixVertexBetheOddPositiveHalfJacobianMatrix N m c q j k‖ < ‖sixVertexBetheOddPositiveHalfJacobianMatrix N m c q j j‖) :
-- imply
  Function.Injective (sixVertexOddSymmetricBetheRootJacobian N m c q) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricBetheRootJacobian_injective_of_diagonalDominance hc q hdom


-- created on 2026-10-23
