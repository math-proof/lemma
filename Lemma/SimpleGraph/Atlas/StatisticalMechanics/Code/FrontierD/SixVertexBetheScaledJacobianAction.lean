import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScaledJacobianAction
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexBethePositiveHalfScaledJacobianMatrix_mulVec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheScaledJacobianAction.lean)
-/
@[path]
private lemma sixVertexBethePositiveHalfScaledJacobianMatrix_mulVec_eq
  {N m : Nat}
  {c : Real}
-- given
  (hc : 2 < c)
  (q : Fin m -> Real)
  (v : Fin m -> Real) :
-- imply
  (sixVertexBethePositiveHalfScaledJacobianMatrix N m c q).mulVec v = sixVertexEvenSymmetricBetheRootJacobian N m c q (fun k => sixVertexPositiveHalfRootGap q k * v k) := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePositiveHalfScaledJacobianMatrix_mulVec hc q v


-- created on 2026-10-23
