import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualPrimalPointDisjoint
open StatMech StatMech.FrontierD


/--
[FKRectIntegralDartListUsesPoint.of_mem_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalPointDisjoint.lean)
-/
@[path]
private lemma of_mem_source_eq
  {l : List FKRectIntegralSquareDart}
  {d : FKRectIntegralSquareDart}
-- given
  (hd : d ∈ l) :
-- imply
  FKRectIntegralDartListUsesPoint l d.1 := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralDartListUsesPoint.of_mem_source hd

/--
[FKRectIntegralDartListUsesPoint.of_mem_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalPointDisjoint.lean)
-/
@[path]
private lemma of_mem_end_eq
  {l : List FKRectIntegralSquareDart}
  {d : FKRectIntegralSquareDart}
-- given
  (hd : d ∈ l) :
-- imply
  FKRectIntegralDartListUsesPoint l (fkRectIntegralSquareDartEnd d) := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralDartListUsesPoint.of_mem_end hd

/--
[fkRectIntegralDartListUsesPoint_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalPointDisjoint.lean)
-/
@[path]
private lemma fkRectIntegralDartListUsesPoint_append_eq
  {l k : List FKRectIntegralSquareDart}
  {p : Int × Int} :
-- imply
  FKRectIntegralDartListUsesPoint (l ++ k) p ↔ FKRectIntegralDartListUsesPoint l p ∨ FKRectIntegralDartListUsesPoint k p := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralDartListUsesPoint_append l k p

/--
[fkRectIntegralDartListUsesPoint_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalPointDisjoint.lean)
-/
@[path]
private lemma fkRectIntegralDartListUsesPoint_reverse_eq
  {l : List FKRectIntegralSquareDart}
  {p : Int × Int} :
-- imply
  FKRectIntegralDartListUsesPoint (fkRectIntegralSquareDartListReverse l) p ↔ FKRectIntegralDartListUsesPoint l p := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralDartListUsesPoint_reverse l p

/--
[fkRectRefined_perpendicular_centerlines_center_eq_of_integral_commonPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalPointDisjoint.lean)
-/
@[path]
private lemma fkRectRefined_perpendicular_centerlines_center_eq_of_integral_commonPoint_eq
  {pairing : Bool}
  {c z p : Int × Int}
-- given
  (hc : FKRectRefinedEdgeCenterNormal pairing c)
  (hz : FKRectRefinedEdgeCenterNormal pairing z)
  (hl : FKRectIntegralDartListUsesPoint (fkRectRefinedPrimalCenterlineDarts (!pairing) c) p)
  (hr : FKRectIntegralDartListUsesPoint (fkRectRefinedPrimalCenterlineDarts pairing z) p) :
-- imply
  c = z := by
-- proof
  apply StatMech.FrontierD.fkRectRefined_perpendicular_centerlines_center_eq_of_integral_commonPoint pairing c z p hc hz hl hr

/--
[fkRectRefined_parallel_oppositeNormal_centerlines_pointDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalPointDisjoint.lean)
-/
@[path]
private lemma fkRectRefined_parallel_oppositeNormal_centerlines_pointDisjoint_eq
  {pairing : Bool}
  {c z p : Int × Int}
-- given
  (hc : FKRectRefinedEdgeCenterNormal (!pairing) c)
  (hz : FKRectRefinedEdgeCenterNormal pairing z)
  (hl : FKRectIntegralDartListUsesPoint (fkRectRefinedPrimalCenterlineDarts pairing c) p) :
-- imply
  ¬ FKRectIntegralDartListUsesPoint (fkRectRefinedPrimalCenterlineDarts pairing z) p := by
-- proof
  apply StatMech.FrontierD.fkRectRefined_parallel_oppositeNormal_centerlines_pointDisjoint pairing c z p hc hz hl

/--
[fkRectRefined_dualOpen_primalOpen_edgeBlocks_pointDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalPointDisjoint.lean)
-/
@[path]
private lemma fkRectRefined_dualOpen_primalOpen_edgeBlocks_pointDisjoint_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d e : R.EdgeIndex}
  {u v : Int × Int}
-- given
  (hd : fkRectDualConfigurationEquiv R omega d = true)
  (he : omega e = true) :
-- imply
  ∀ p, FKRectIntegralDartListUsesPoint ((fkRectRefinedDualEdgeDarts R d).map (fkRectIntegralSquareDartTranslate (fkRectRefinedDeckTranslation R u))) p → ¬ FKRectIntegralDartListUsesPoint ((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartTranslate (fkRectRefinedDeckTranslation R v))) p := by
-- proof
  apply StatMech.FrontierD.fkRectRefined_dualOpen_primalOpen_edgeBlocks_pointDisjoint R omega d e hd he u v

/--
[FKRectRefinedOpenEdgeBlocks.pointDisjoint_from_dualEdgeBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalPointDisjoint.lean)
-/
@[path]
private lemma pointDisjoint_from_dualEdgeBlock_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {F : Finset R.EdgeIndex}
  {k : List FKRectIntegralSquareDart}
  {d : R.EdgeIndex}
  {u : Int × Int}
-- given
  (hF : ∀ e, e ∈ F ↔ omega e = true)
  (hk : FKRectRefinedOpenEdgeBlocks R F k)
  (hd : fkRectDualConfigurationEquiv R omega d = true) :
-- imply
  ∀ p, FKRectIntegralDartListUsesPoint ((fkRectRefinedDualEdgeDarts R d).map (fkRectIntegralSquareDartTranslate (fkRectRefinedDeckTranslation R u))) p → ¬ FKRectIntegralDartListUsesPoint k p := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedOpenEdgeBlocks.pointDisjoint_from_dualEdgeBlock R omega F hF hk d u hd

/--
[FKRectRefinedDualOpenEdgeBlocks.pointDisjoint_of_edgeBlocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalPointDisjoint.lean)
-/
@[path]
private lemma pointDisjoint_of_edgeBlocks_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {F : Finset R.EdgeIndex}
  {l k : List FKRectIntegralSquareDart}
-- given
  (hF : ∀ e, e ∈ F ↔ omega e = true)
  (hl : FKRectRefinedDualOpenEdgeBlocks R omega l)
  (hk : FKRectRefinedOpenEdgeBlocks R F k) :
-- imply
  ∀ p, FKRectIntegralDartListUsesPoint l p → ¬ FKRectIntegralDartListUsesPoint k p := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedDualOpenEdgeBlocks.pointDisjoint_of_edgeBlocks R omega F hF hl hk

/--
[FKRectRefinedDualOpenEdgeBlocks.not_incident_of_mem_edgeBlocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalPointDisjoint.lean)
-/
@[path]
private lemma not_incident_of_mem_edgeBlocks_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {F : Finset R.EdgeIndex}
  {l k : List FKRectIntegralSquareDart}
  {d e : FKRectIntegralSquareDart}
-- given
  (hF : ∀ e, e ∈ F ↔ omega e = true)
  (hl : FKRectRefinedDualOpenEdgeBlocks R omega l)
  (hk : FKRectRefinedOpenEdgeBlocks R F k)
  (hd : d ∈ l)
  (he : e ∈ k) :
-- imply
  ¬ FKRectIntegralSquareDartsIncident d e := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedDualOpenEdgeBlocks.not_incident_of_mem_edgeBlocks R omega F hF hl hk hd he


-- created on 2026-10-23
