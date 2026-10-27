import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualEdgeCarrier
open StatMech StatMech.FrontierD


/--
[exists_fkRectRefinedDualEdgeCenter_edgeToDualEdge_eq_add_deck](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualEdgeCarrier.lean)
-/
@[path]
private lemma exists_fkRectRefinedDualEdgeCenter_edgeToDualEdge_eq_add_deck_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  ∃ u : Int × Int, fkRectRefinedDualEdgeCenter R (fkRectEdgeToDualEdge R e) = ((fkRectRefinedPrimalEdgeCenter R e).1 + 4 * (fkRectSquareDeckTranslation R u).1, (fkRectRefinedPrimalEdgeCenter R e).2 + 4 * (fkRectSquareDeckTranslation R u).2) := by
-- proof
  apply StatMech.FrontierD.exists_fkRectRefinedDualEdgeCenter_edgeToDualEdge_eq_add_deck R e

/--
[fkRectRefinedDualEdgeDarts_eq_centerline](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualEdgeCarrier.lean)
-/
@[path]
private lemma fkRectRefinedDualEdgeDarts_eq_centerline_eq
  {R : FKRectTorus}
  {d : R.EdgeIndex} :
-- imply
  fkRectRefinedDualEdgeDarts R d = fkRectRefinedPrimalCenterlineDarts (fkRectClosedPairingAtEdge d) (fkRectRefinedDualEdgeCenter R d) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedDualEdgeDarts_eq_centerline R d

/--
[fkRectRefinedDualEdgeDarts_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualEdgeCarrier.lean)
-/
@[path]
private lemma fkRectRefinedDualEdgeDarts_path_eq
  {R : FKRectTorus}
  {d : R.EdgeIndex} :
-- imply
  FKRectIntegralSquareDartPath (fkRectRefinedDualEdgeStart R d) (fkRectRefinedDualEdgeEnd R d) (fkRectRefinedDualEdgeDarts R d) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedDualEdgeDarts_path R d


-- created on 2026-10-23
