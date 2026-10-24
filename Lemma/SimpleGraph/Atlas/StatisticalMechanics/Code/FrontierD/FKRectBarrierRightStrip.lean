import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectBarrierRightStrip
open StatMech StatMech.FrontierD


/--
[FKRectDependsOnOutsideRegion.inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBarrierRightStrip.lean)
-/
@[path]
private lemma inter_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {A B : Set R.Configuration}
-- given
  (hA : FKRectDependsOnOutsideRegion R S A)
  (hB : FKRectDependsOnOutsideRegion R S B) :
-- imply
  FKRectDependsOnOutsideRegion R S (A ∩ B) := by
-- proof
  apply StatMech.FrontierD.FKRectDependsOnOutsideRegion.inter R S hA hB

/--
[FKRectDependsOnOutsideRegion.compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBarrierRightStrip.lean)
-/
@[path]
private lemma compl_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {A : Set R.Configuration}
-- given
  (hA : FKRectDependsOnOutsideRegion R S A) :
-- imply
  FKRectDependsOnOutsideRegion R S Aᶜ := by
-- proof
  apply StatMech.FrontierD.FKRectDependsOnOutsideRegion.compl R S hA

/--
[fkRect_inducedOpenGraph_eq_of_agreesOutside_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBarrierRightStrip.lean)
-/
@[path]
private lemma fkRect_inducedOpenGraph_eq_of_agreesOutside_disjoint_eq
  {R : FKRectTorus}
  {S T : Set R.Vertex}
  {omega tau : R.Configuration}
-- given
  (hdisj : ∀ v, v ∈ T → v ∉ S)
  (hot : ∀ a : R.EdgeIndex, fkRectTorusIndexedEdge R a ∉ Set.range (FK.ocd_innerEdge (Subtype.val : FKRectInducedVertex R S → R.Vertex)) → omega a = tau a) :
-- imply
  (fkRectOpenGraph R omega).induce T = (fkRectOpenGraph R tau).induce T := by
-- proof
  apply StatMech.FrontierD.fkRect_inducedOpenGraph_eq_of_agreesOutside_disjoint R S T hdisj omega tau hot

/--
[fkRectSetConnectionWithinEvent_dependsOnOutsideRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBarrierRightStrip.lean)
-/
@[path]
private lemma fkRectSetConnectionWithinEvent_dependsOnOutsideRegion_eq
  {R : FKRectTorus}
  {S T X Y : Set R.Vertex}
-- given
  (hdisj : ∀ v, v ∈ T → v ∉ S) :
-- imply
  FKRectDependsOnOutsideRegion R S (fkRectSetConnectionWithinEvent R T X Y) := by
-- proof
  apply StatMech.FrontierD.fkRectSetConnectionWithinEvent_dependsOnOutsideRegion R S T X Y hdisj

/--
[fkRectSetConnectionWithinEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBarrierRightStrip.lean)
-/
@[path]
private lemma fkRectSetConnectionWithinEvent_isIncreasing_eq
  {R : FKRectTorus}
  {T X Y : Set R.Vertex} :
-- imply
  IsIncreasing (fkRectSetConnectionWithinEvent R T X Y) := by
-- proof
  apply StatMech.FrontierD.fkRectSetConnectionWithinEvent_isIncreasing R T X Y

/--
[fkRectNoLeftStripCrossingEvent_isDecreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBarrierRightStrip.lean)
-/
@[path]
private lemma fkRectNoLeftStripCrossingEvent_isDecreasing_eq
  {R : FKRectTorus}
  {right : Nat} :
-- imply
  IsDecreasing (fkRectNoLeftStripCrossingEvent R right) := by
-- proof
  apply StatMech.FrontierD.fkRectNoLeftStripCrossingEvent_isDecreasing R right

/--
[fkRectNoLeftStripCrossing_dependsOnOutsideRightStripBand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBarrierRightStrip.lean)
-/
@[path]
private lemma fkRectNoLeftStripCrossing_dependsOnOutsideRightStripBand_eq
  {R : FKRectTorus}
  {leftRight cut lower upper : Nat}
-- given
  (hsep : leftRight < cut) :
-- imply
  FKRectDependsOnOutsideRegion R (fkRectRightStripBand R cut lower upper) (fkRectNoLeftStripCrossingEvent R leftRight) := by
-- proof
  apply StatMech.FrontierD.fkRectNoLeftStripCrossing_dependsOnOutsideRightStripBand R leftRight cut lower upper hsep

/--
[fkRectLeftBarrierWithSeamPattern_dependsOnOutsideRightStripBand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBarrierRightStrip.lean)
-/
@[path]
private lemma fkRectLeftBarrierWithSeamPattern_dependsOnOutsideRightStripBand_eq
  {R : FKRectTorus}
  {leftRight cut lower upper : Nat}
  {I : Finset R.EdgeIndex}
  {eta : R.Configuration}
-- given
  (hsep : leftRight < cut)
  (hlower : 1 ≤ lower)
  (hI : ∀ a ∈ I, fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a)) :
-- imply
  FKRectDependsOnOutsideRegion R (fkRectRightStripBand R cut lower upper) (fkRectLeftBarrierWithSeamPattern R leftRight I eta) := by
-- proof
  apply StatMech.FrontierD.fkRectLeftBarrierWithSeamPattern_dependsOnOutsideRightStripBand R leftRight cut lower upper hsep hlower I hI eta


-- created on 2026-10-23
