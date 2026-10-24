import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualPrimalOpenInteraction
open StatMech StatMech.FrontierD


/--
[fkRectRefined_perpendicular_centerlines_center_mod_eq_of_commonPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalOpenInteraction.lean)
-/
@[path]
private lemma fkRectRefined_perpendicular_centerlines_center_mod_eq_of_commonPoint_eq
  {R : FKRectTorus}
  {pairing : Bool}
  {c z : Int × Int}
  {p : ZMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)) × ZMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R))}
-- given
  (hc : FKRectRefinedEdgeCenterNormal pairing c)
  (hz : FKRectRefinedEdgeCenterNormal pairing z)
  (hl : FKRectDartListUsesPoint ((fkRectRefinedPrimalCenterlineDarts (!pairing) c).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p)
  (hr : FKRectDartListUsesPoint ((fkRectRefinedPrimalCenterlineDarts pairing z).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p) :
-- imply
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) = (((z.1 : Int) : ZMod L), ((z.2 : Int) : ZMod L)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefined_perpendicular_centerlines_center_mod_eq_of_commonPoint R pairing c z hc hz p hl hr

/--
[fkRectRefined_perpendicular_legal_centerlines_interaction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalOpenInteraction.lean)
-/
@[path]
private lemma fkRectRefined_perpendicular_legal_centerlines_interaction_eq
  {R : FKRectTorus}
  {pairing : Bool}
  {c z : Int × Int}
-- given
  (hc : FKRectRefinedEdgeCenterNormal pairing c)
  (hz : FKRectRefinedEdgeCenterNormal pairing z) :
-- imply
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) fkRectRefinedRawInteraction ((fkRectRefinedPrimalCenterlineDarts (!pairing) c).map (fkRectIntegralSquareDartMod L)) ((fkRectRefinedPrimalCenterlineDarts pairing z).map (fkRectIntegralSquareDartMod L)) = if (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) = (((z.1 : Int) : ZMod L), ((z.2 : Int) : ZMod L)) then if pairing then 1 else -1 else 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefined_perpendicular_legal_centerlines_interaction R pairing c z hc hz

/--
[fkRectRefined_parallel_centerlines_interaction_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalOpenInteraction.lean)
-/
@[path]
private lemma fkRectRefined_parallel_centerlines_interaction_eq_zero_eq
  {L : Nat}
  [Fact (8 < L)]
  {pairing : Bool}
  {c z : Int × Int} :
-- imply
  fkRectRefinedRawInteraction ((fkRectRefinedPrimalCenterlineDarts pairing c).map (fkRectIntegralSquareDartMod L)) ((fkRectRefinedPrimalCenterlineDarts pairing z).map (fkRectIntegralSquareDartMod L)) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefined_parallel_centerlines_interaction_eq_zero pairing c z

/--
[fkRectRefinedPrimalCenterlineDarts_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalOpenInteraction.lean)
-/
@[path]
private lemma fkRectRefinedPrimalCenterlineDarts_translate_eq
  {pairing : Bool}
  {c t : Int × Int} :
-- imply
  (fkRectRefinedPrimalCenterlineDarts pairing c).map (fkRectIntegralSquareDartTranslate t) = fkRectRefinedPrimalCenterlineDarts pairing (c.1 + t.1, c.2 + t.2) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedPrimalCenterlineDarts_translate pairing c t

/--
[fkRectRefinedDualEdgeCenter_normal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalOpenInteraction.lean)
-/
@[path]
private lemma fkRectRefinedDualEdgeCenter_normal_eq
  {R : FKRectTorus}
  {d : R.EdgeIndex} :
-- imply
  FKRectRefinedEdgeCenterNormal (!(fkRectClosedPairingAtEdge d)) (fkRectRefinedDualEdgeCenter R d) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedDualEdgeCenter_normal R d

/--
[fkRectRefinedDualEdgeCenter_deck_normal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalOpenInteraction.lean)
-/
@[path]
private lemma fkRectRefinedDualEdgeCenter_deck_normal_eq
  {R : FKRectTorus}
  {d : R.EdgeIndex}
  {u : Int × Int} :
-- imply
  FKRectRefinedEdgeCenterNormal (!(fkRectClosedPairingAtEdge d)) ((fkRectRefinedDualEdgeCenter R d).1 + (fkRectRefinedDeckTranslation R u).1, (fkRectRefinedDualEdgeCenter R d).2 + (fkRectRefinedDeckTranslation R u).2) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedDualEdgeCenter_deck_normal R d u

/--
[fkRectIndexedEdge_eq_of_refinedCenter_twoDeck_mod_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalOpenInteraction.lean)
-/
@[path]
private lemma fkRectIndexedEdge_eq_of_refinedCenter_twoDeck_mod_eq_eq
  {R : FKRectTorus}
  {e f : R.EdgeIndex}
  {u v : Int × Int}
-- given
  (hmod : let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let c := fkRectRefinedPrimalEdgeCenter R e let z := fkRectRefinedPrimalEdgeCenter R f (((c.1 + (fkRectRefinedDeckTranslation R u).1 : Int) : ZMod L), ((c.2 + (fkRectRefinedDeckTranslation R u).2 : Int) : ZMod L)) = (((z.1 + (fkRectRefinedDeckTranslation R v).1 : Int) : ZMod L), ((z.2 + (fkRectRefinedDeckTranslation R v).2 : Int) : ZMod L))) :
-- imply
  e = f := by
-- proof
  apply StatMech.FrontierD.fkRectIndexedEdge_eq_of_refinedCenter_twoDeck_mod_eq R e f u v hmod

/--
[fkRectDualEdge_eq_edgeToDualEdge_of_refinedCenter_deck_mod_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalOpenInteraction.lean)
-/
@[path]
private lemma fkRectDualEdge_eq_edgeToDualEdge_of_refinedCenter_deck_mod_eq_eq
  {R : FKRectTorus}
  {d e : R.EdgeIndex}
  {u v : Int × Int}
-- given
  (hmod : let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) ((((fkRectRefinedDualEdgeCenter R d).1 + (fkRectRefinedDeckTranslation R u).1 : Int) : ZMod L), (((fkRectRefinedDualEdgeCenter R d).2 + (fkRectRefinedDeckTranslation R u).2 : Int) : ZMod L)) = ((((fkRectRefinedPrimalEdgeCenter R e).1 + (fkRectRefinedDeckTranslation R v).1 : Int) : ZMod L), (((fkRectRefinedPrimalEdgeCenter R e).2 + (fkRectRefinedDeckTranslation R v).2 : Int) : ZMod L))) :
-- imply
  d = fkRectEdgeToDualEdge R e := by
-- proof
  apply StatMech.FrontierD.fkRectDualEdge_eq_edgeToDualEdge_of_refinedCenter_deck_mod_eq R d e u v hmod

/--
[fkRectRefinedDualOpen_primalOpen_centers_mod_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalOpenInteraction.lean)
-/
@[path]
private lemma fkRectRefinedDualOpen_primalOpen_centers_mod_ne_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d e : R.EdgeIndex}
  {u v : Int × Int}
-- given
  (hd : fkRectDualConfigurationEquiv R omega d = true)
  (he : omega e = true) :
-- imply
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let c : ZMod L × ZMod L := ((fkRectRefinedDualEdgeCenter R d).1 + (fkRectRefinedDeckTranslation R u).1, (fkRectRefinedDualEdgeCenter R d).2 + (fkRectRefinedDeckTranslation R u).2) let z : ZMod L × ZMod L := ((fkRectRefinedPrimalEdgeCenter R e).1 + (fkRectRefinedDeckTranslation R v).1, (fkRectRefinedPrimalEdgeCenter R e).2 + (fkRectRefinedDeckTranslation R v).2) c ≠ z := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedDualOpen_primalOpen_centers_mod_ne R omega d e hd he u v

/--
[fkRectRefined_dualOpen_primalOpen_edgeBlocks_interaction_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalOpenInteraction.lean)
-/
@[path]
private lemma fkRectRefined_dualOpen_primalOpen_edgeBlocks_interaction_eq_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d e : R.EdgeIndex}
  {u v : Int × Int}
-- given
  (hd : fkRectDualConfigurationEquiv R omega d = true)
  (he : omega e = true) :
-- imply
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) fkRectRefinedRawInteraction (((fkRectRefinedDualEdgeDarts R d).map (fkRectIntegralSquareDartTranslate (fkRectRefinedDeckTranslation R u))).map (fkRectIntegralSquareDartMod L)) (((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartTranslate (fkRectRefinedDeckTranslation R v))).map (fkRectIntegralSquareDartMod L)) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefined_dualOpen_primalOpen_edgeBlocks_interaction_eq_zero R omega d e hd he u v


-- created on 2026-10-23
