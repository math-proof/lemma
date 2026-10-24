import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectAugmentedSourceBarrier
open StatMech StatMech.FrontierD


/--
[fkRectAugmentedSourcePatternEdges_outsideRightBand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedSourceBarrier.lean)
-/
@[path]
private lemma fkRectAugmentedSourcePatternEdges_outsideRightBand_eq
  {R : FKRectTorus}
  {cut : Nat}
  {x : Fin R.width}
  {a : R.EdgeIndex}
-- given
  (ha : a ∈ fkRectAugmentedSourcePatternEdges R x) :
-- imply
  fkRectTorusIndexedEdge R a ∉ Set.range (FK.ocd_innerEdge (Subtype.val : FKRectRightStripBandVertex R cut 1 (R.height - 1) → R.Vertex)) := by
-- proof
  apply StatMech.FrontierD.fkRectAugmentedSourcePatternEdges_outsideRightBand R cut x a ha

/--
[fkRectAugmentedSourceBarrier_dependsOnOutsideRightBand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedSourceBarrier.lean)
-/
@[path]
private lemma fkRectAugmentedSourceBarrier_dependsOnOutsideRightBand_eq
  {R : FKRectTorus}
  {leftRight cut : Nat}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
-- given
  (hsep : leftRight < cut) :
-- imply
  FKRectDependsOnOutsideRegion R (fkRectRightStripBand R cut 1 (R.height - 1)) (fkRectAugmentedSourceBarrier R leftRight gap x) := by
-- proof
  apply StatMech.FrontierD.fkRectAugmentedSourceBarrier_dependsOnOutsideRightBand R leftRight cut hsep gap x

/--
[fkRectAugmentedSourceBarrier_witnessEdges_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedSourceBarrier.lean)
-/
@[path]
private lemma fkRectAugmentedSourceBarrier_witnessEdges_open_eq
  {R : FKRectTorus}
  {leftRight : Nat}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {omega : R.Configuration}
-- given
  (hgap : gap ∈ fkRectHorizontalCutEdges R)
  (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
  (homega : omega ∈ fkRectAugmentedSourceBarrier R leftRight gap x) :
-- imply
  omega (fkRectVerticalSeamEdgeAt R x) = true ∧ omega (fkRectRowZeroAttachmentEdgeAt R x) = true := by
-- proof
  apply StatMech.FrontierD.fkRectAugmentedSourceBarrier_witnessEdges_open R leftRight hgap x hchosen homega

/--
[fkRectAugmentedSource_barrierConnectionProduct_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedSourceBarrier.lean)
-/
@[path]
private lemma fkRectAugmentedSource_barrierConnectionProduct_le_eq
  {R : FKRectTorus}
  {leftRight cut : Nat}
  {q : Real}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hsep : leftRight < cut)
  (hq : 1 ≤ q) :
-- imply
  (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2) * fkRectCriticalEventMass R q (fkRectAugmentedSourceBarrier R leftRight gap x) ≤ ∑ rho, (fkRectAugmentedBarrierConnectionEvent R leftRight cut gap x t).indicator (fun _ => (1 : Real)) rho * FK.fkProb (fkRectTorusGraph R) (fkRectCriticalP q) q rho := by
-- proof
  apply StatMech.FrontierD.fkRectAugmentedSource_barrierConnectionProduct_le R leftRight cut hsep hq gap x t


-- created on 2026-10-23
