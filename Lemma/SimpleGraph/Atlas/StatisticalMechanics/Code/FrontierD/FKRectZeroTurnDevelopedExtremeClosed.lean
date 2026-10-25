import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedExtremeClosed
open StatMech StatMech.FrontierD


/--
[fkRectRawPrimalCrossingDevelopedExtremeDart_edge_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedExtremeClosed.lean)
-/
@[path]
private lemma fkRectRawPrimalCrossingDevelopedExtremeDart_edge_closed_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawPrimalHorizontalCrossingComponent R omega}
  {side : Bool} :
-- imply
  omega (fkRectTorusMedialEdgeEquiv R (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side).1) = false := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalCrossingDevelopedExtremeDart_edge_closed R omega C X side


-- created on 2026-10-23
