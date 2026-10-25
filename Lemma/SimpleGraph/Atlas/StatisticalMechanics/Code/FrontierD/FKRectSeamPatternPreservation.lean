import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamPatternPreservation.Part2
open StatMech StatMech.FrontierD


/--
[fkRectForceIndexedPattern_innerRestrict_eq_of_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamPatternPreservation.lean)
-/
@[path]
private lemma fkRectForceIndexedPattern_innerRestrict_eq_of_outside_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {I : Finset R.EdgeIndex}
  {eta omega : R.Configuration}
-- given
  (hI : ∀ a ∈ I, fkRectTorusIndexedEdge R a ∉ Set.range (FK.ocd_innerEdge (Subtype.val : FKRectInducedVertex R S -> R.Vertex))) :
-- imply
  FK.ocd_innerRestrict (Subtype.val : FKRectInducedVertex R S -> R.Vertex) (fkRectFullGraphConfiguration R (fkRectForceIndexedPattern R I eta omega)) = FK.ocd_innerRestrict (Subtype.val : FKRectInducedVertex R S -> R.Vertex) (fkRectFullGraphConfiguration R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectForceIndexedPattern_innerRestrict_eq_of_outside R S I eta omega hI

/--
[fkRectForceHorizontalCut_innerRestrict_rightBand_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamPatternPreservation.lean)
-/
@[path]
private lemma fkRectForceHorizontalCut_innerRestrict_rightBand_eq_eq
  {R : FKRectTorus}
  {cut lower upper : Nat}
  {eta omega : R.Configuration}
-- given
  (hlower : 1 <= lower) :
-- imply
  FK.ocd_innerRestrict (Subtype.val : FKRectRightStripBandVertex R cut lower upper -> R.Vertex) (fkRectFullGraphConfiguration R (fkRectForceIndexedPattern R (fkRectHorizontalCutEdges R) eta omega)) = FK.ocd_innerRestrict (Subtype.val : FKRectRightStripBandVertex R cut lower upper -> R.Vertex) (fkRectFullGraphConfiguration R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectForceHorizontalCut_innerRestrict_rightBand_eq R cut lower upper hlower eta omega

/--
[fkRectForceDualPullbackSeam_preserves_rightBand_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamPatternPreservation.lean)
-/
@[path]
private lemma fkRectForceDualPullbackSeam_preserves_rightBand_chain_eq
  {R : FKRectTorus}
  {cut lower upper : Nat}
  {eta omega : R.Configuration}
  {t : Finset (FKRectRightStripBandVertex R cut lower upper × FKRectRightStripBandVertex R cut lower upper)}
-- given
  (hlower : 1 <= lower)
  (hchain : FK.ocd_innerRestrict (Subtype.val : FKRectRightStripBandVertex R cut lower upper -> R.Vertex) (fkRectFullGraphConfiguration R omega) ∈ fkRectInducedConnectionChainEvent R (fkRectRightStripBand R cut lower upper) t) :
-- imply
  FK.ocd_innerRestrict (Subtype.val : FKRectRightStripBandVertex R cut lower upper -> R.Vertex) (fkRectFullGraphConfiguration R (fkRectForceIndexedPattern R (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) eta omega)) ∈ fkRectInducedConnectionChainEvent R (fkRectRightStripBand R cut lower upper) t := by
-- proof
  apply StatMech.FrontierD.fkRectForceDualPullbackSeam_preserves_rightBand_chain R cut lower upper hlower eta omega t hchain

/--
[fkRectDualPullbackUnitGap_eq_verticalSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamPatternPreservation.lean)
-/
@[path]
private lemma fkRectDualPullbackUnitGap_eq_verticalSeam_eq
  {R : FKRectTorus} :
-- imply
  fkRectDualEdgeToEdge R (fkRectUnitLeftBarrierGap R) = fkRectVerticalSeamEdgeAt R (fkRectUnitGapColumn R) := by
-- proof
  apply StatMech.FrontierD.fkRectDualPullbackUnitGap_eq_verticalSeam R

/--
[fkRectEdgeToDualEdge_unitVerticalSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamPatternPreservation.lean)
-/
@[path]
private lemma fkRectEdgeToDualEdge_unitVerticalSeam_eq
  {R : FKRectTorus} :
-- imply
  fkRectEdgeToDualEdge R (fkRectVerticalSeamEdgeAt R (fkRectUnitGapColumn R)) = fkRectUnitLeftBarrierGap R := by
-- proof
  apply StatMech.FrontierD.fkRectEdgeToDualEdge_unitVerticalSeam R

/--
[fkRectForceDualPullbackUnitPattern_verticalSeam_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamPatternPreservation.lean)
-/
@[path]
private lemma fkRectForceDualPullbackUnitPattern_verticalSeam_open_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectForceIndexedPattern R (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) (fkRectDualPullbackConfiguration R (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R))) omega (fkRectVerticalSeamEdgeAt R (fkRectUnitGapColumn R)) = true := by
-- proof
  apply StatMech.FrontierD.fkRectForceDualPullbackUnitPattern_verticalSeam_open R omega

/--
[fkRectForceDualPullbackUnitPattern_attachment_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamPatternPreservation.lean)
-/
@[path]
private lemma fkRectForceDualPullbackUnitPattern_attachment_eq_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectForceIndexedPattern R (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) (fkRectDualPullbackConfiguration R (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R))) omega (fkRectRowZeroAttachmentEdgeAt R (fkRectUnitGapColumn R)) = omega (fkRectRowZeroAttachmentEdgeAt R (fkRectUnitGapColumn R)) := by
-- proof
  apply StatMech.FrontierD.fkRectForceDualPullbackUnitPattern_attachment_eq R omega

/--
[fkRectForceDualPullbackUnitPattern_verticalWinding_of_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamPatternPreservation.lean)
-/
@[path]
private lemma fkRectForceDualPullbackUnitPattern_verticalWinding_of_chain_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {t : Finset (FKRectRightStripBandVertex R 1 1 (R.height - 1) × FKRectRightStripBandVertex R 1 1 (R.height - 1))}
-- given
  (hpair : (fkRectRightBandRowOne R 1 (fkRectUnitGapColumn R) (by rfl), fkRectRightBandLastRow R 1 (fkRectUnitGapColumn R) (by rfl)) ∈ t)
  (hchain : FK.ocd_innerRestrict (Subtype.val : FKRectRightStripBandVertex R 1 1 (R.height - 1) -> R.Vertex) (fkRectFullGraphConfiguration R omega) ∈ fkRectInducedConnectionChainEvent R (fkRectRightStripBand R 1 1 (R.height - 1)) t)
  (hattach : omega (fkRectRowZeroAttachmentEdgeAt R (fkRectUnitGapColumn R)) = true) :
-- imply
  fkRectForceIndexedPattern R (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) (fkRectDualPullbackConfiguration R (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R))) omega ∈ fkRectVerticalWindingEvent R := by
-- proof
  apply StatMech.FrontierD.fkRectForceDualPullbackUnitPattern_verticalWinding_of_chain R omega t hpair hchain hattach


-- created on 2026-10-23
