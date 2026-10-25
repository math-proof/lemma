import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDistinctEdgeSupport
open StatMech StatMech.FrontierD


/--
[fkRectRefinedCenter_mod_eq_of_closed_local_centerline_commonPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDistinctEdgeSupport.lean)
-/
@[path]
private lemma fkRectRefinedCenter_mod_eq_of_closed_local_centerline_commonPoint_eq
  {R : FKRectTorus}
  {closed targetHorizontal : Bool}
  {c z : Int × Int}
  {side : FKMedialSide}
  {p : ZMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)) × ZMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R))}
-- given
  (hc : FKRectRefinedEdgeCenterNormal closed c)
  (hz : FKRectRefinedEdgeCenterNormal targetHorizontal z)
  (hl : FKRectDartListUsesPoint ((fkRectRefinedLocalDarts closed c side).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p)
  (ht : FKRectDartListUsesPoint ((fkRectRefinedPrimalCenterlineDarts targetHorizontal z).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p) :
-- imply
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) = (((z.1 : Int) : ZMod L), ((z.2 : Int) : ZMod L)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedCenter_mod_eq_of_closed_local_centerline_commonPoint R closed targetHorizontal c z side hc hz p hl ht

/--
[fkRectRefinedBoundaryLocal_endpointDisjoint_of_closed_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDistinctEdgeSupport.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryLocal_endpointDisjoint_of_closed_ne_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus}
  {c : Int × Int}
  {e f : R.EdgeIndex}
  {u : Int × Int}
-- given
  (hcurrent : fkRectTorusMedialEdgeEquiv R d.1 = f)
  (hclosed : pairing d.1 = fkRectClosedPairingAtEdge f)
  (hcenter : c = ((fkRectRefinedPrimalEdgeCenter R f).1 + 4 * (fkRectSquareDeckTranslation R u).1, (fkRectRefinedPrimalEdgeCenter R f).2 + 4 * (fkRectSquareDeckTranslation R u).2))
  (hne : f ≠ e) :
-- imply
  ∀ p, FKRectDartListUsesPoint ((fkRectRefinedLocalDarts (pairing d.1) c d.2).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p → ¬ FKRectDartListUsesPoint ((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryLocal_endpointDisjoint_of_closed_ne R pairing d c e f u hcurrent hclosed hcenter hne

/--
[fkRectRefinedBoundaryLocalInteraction_eq_zero_of_closed_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDistinctEdgeSupport.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryLocalInteraction_eq_zero_of_closed_ne_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus}
  {c : Int × Int}
  {e f : R.EdgeIndex}
  {u : Int × Int}
-- given
  (hcurrent : fkRectTorusMedialEdgeEquiv R d.1 = f)
  (hclosed : pairing d.1 = fkRectClosedPairingAtEdge f)
  (hcenter : c = ((fkRectRefinedPrimalEdgeCenter R f).1 + 4 * (fkRectSquareDeckTranslation R u).1, (fkRectRefinedPrimalEdgeCenter R f).2 + 4 * (fkRectSquareDeckTranslation R u).2))
  (hne : f ≠ e) :
-- imply
  fkRectRefinedBoundaryLocalInteraction R pairing d c e = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryLocalInteraction_eq_zero_of_closed_ne R pairing d c e f u hcurrent hclosed hcenter hne


-- created on 2026-10-23
