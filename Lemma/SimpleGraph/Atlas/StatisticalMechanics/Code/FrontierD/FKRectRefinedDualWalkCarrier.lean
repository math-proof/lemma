import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualWalkCarrier.Part2
open StatMech StatMech.FrontierD


/--
[FKRectRefinedDualWalkCarrier.path_translation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualWalkCarrier.lean)
-/
@[path]
private lemma path_translation_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x y}
  {p q : Int × Int}
  {h : FKRectSquareWalkLift R w p q}
  {D : FKRectRefinedDualWalkCarrier R h} :
-- imply
  FKRectIntegralSquareDartPath (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)) ((fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)).1 + D.translation.1, (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)).2 + D.translation.2) D.darts := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedDualWalkCarrier.path_translation D

/--
[FKRectRefinedDualWalkCarrier.interaction_ne_zero_iff_windingIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualWalkCarrier.lean)
-/
@[path]
private lemma interaction_ne_zero_iff_windingIndependent_eq
  {R : FKRectTorus}
  {G H : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {z : G.Walk x x}
  {w : H.Walk y y}
  {p q a b : Int × Int}
  {hz : FKRectSquareWalkLift R z p q}
  {hw : FKRectSquareWalkLift R w a b}
  {D : FKRectRefinedDualWalkCarrier R hz}
  {C : FKRectRefinedWalkCarrier R hw} :
-- imply
  fkRectRefinedRawInteraction D.coverDarts C.coverDarts ≠ 0 ↔ FKRectWindingIndependent (fkRectWalkWinding R z) (fkRectWalkWinding R w) := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedDualWalkCarrier.interaction_ne_zero_iff_windingIndependent R D C


-- created on 2026-10-23
