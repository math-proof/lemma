import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedEdgeCenterClass
open StatMech StatMech.FrontierD


/--
[fkRectRefinedPrimalEdgeCenter_eq_firstLift_normalForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedEdgeCenterClass.lean)
-/
@[path]
private lemma fkRectRefinedPrimalEdgeCenter_eq_firstLift_normalForm_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  let p := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1 fkRectRefinedPrimalEdgeCenter R e = if fkRectClosedPairingAtEdge e then (4 * p.1 - 2, 4 * p.2) else (4 * p.1, 4 * p.2 + 2) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedPrimalEdgeCenter_eq_firstLift_normalForm R e

/--
[fkRectIndexedEdge_eq_of_closedPairing_eq_of_firstLift_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedEdgeCenterClass.lean)
-/
@[path]
private lemma fkRectIndexedEdge_eq_of_closedPairing_eq_of_firstLift_eq_eq
  {R : FKRectTorus}
  {e f : R.EdgeIndex}
-- given
  (hpair : fkRectClosedPairingAtEdge e = fkRectClosedPairingAtEdge f)
  (hfirst : fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).1 = fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R f).1) :
-- imply
  e = f := by
-- proof
  apply StatMech.FrontierD.fkRectIndexedEdge_eq_of_closedPairing_eq_of_firstLift_eq R e f hpair hfirst

/--
[fkRectIndexedEdge_eq_of_refinedCenter_deck_mod_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedEdgeCenterClass.lean)
-/
@[path]
private lemma fkRectIndexedEdge_eq_of_refinedCenter_deck_mod_eq_eq
  {R : FKRectTorus}
  {e f : R.EdgeIndex}
  {u : Int × Int}
-- given
  (hmod : let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let c := fkRectRefinedPrimalEdgeCenter R e let z := fkRectRefinedPrimalEdgeCenter R f let A := fkRectSquareDeckTranslation R u (((c.1 + 4 * A.1 : Int) : ZMod L), ((c.2 + 4 * A.2 : Int) : ZMod L)) = (((z.1 : Int) : ZMod L), ((z.2 : Int) : ZMod L))) :
-- imply
  e = f := by
-- proof
  apply StatMech.FrontierD.fkRectIndexedEdge_eq_of_refinedCenter_deck_mod_eq R e f u hmod


-- created on 2026-10-23
