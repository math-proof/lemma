import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedWalkCarrier.Part3
open StatMech StatMech.FrontierD


/--
[FKRectSquareWalkLift.exists_refinedWalkCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedWalkCarrier.lean)
-/
@[path]
private lemma exists_refinedWalkCarrier_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x y}
  {p q : Int × Int}
-- given
  (h : FKRectSquareWalkLift R w p q) :
-- imply
  Nonempty (FKRectRefinedWalkCarrier R h) := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.exists_refinedWalkCarrier R h

/--
[FKRectRefinedWalkCarrier.path_translation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedWalkCarrier.lean)
-/
@[path]
private lemma path_translation_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x y}
  {p q : Int × Int}
  {h : FKRectSquareWalkLift R w p q}
  {C : FKRectRefinedWalkCarrier R h} :
-- imply
  FKRectIntegralSquareDartPath (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)) ((fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).1 + C.translation.1, (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).2 + C.translation.2) C.darts := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedWalkCarrier.path_translation C

/--
[FKRectRefinedWalkCarrier.interaction_ne_zero_iff_windingIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedWalkCarrier.lean)
-/
@[path]
private lemma interaction_ne_zero_iff_windingIndependent_eq
  {R : FKRectTorus}
  {G H : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x x}
  {z : H.Walk y y}
  {p q a b : Int × Int}
  {hw : FKRectSquareWalkLift R w p q}
  {hz : FKRectSquareWalkLift R z a b}
  {C : FKRectRefinedWalkCarrier R hw}
  {D : FKRectRefinedWalkCarrier R hz} :
-- imply
  fkRectRefinedRawInteraction C.coverDarts D.coverDarts ≠ 0 ↔ FKRectWindingIndependent (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedWalkCarrier.interaction_ne_zero_iff_windingIndependent R C D


-- created on 2026-10-23
