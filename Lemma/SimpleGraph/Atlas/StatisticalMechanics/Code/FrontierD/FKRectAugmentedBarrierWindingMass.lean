import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierWindingMass
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectFullGraphEvent_to_indexed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedBarrierWindingMass.lean)
-/
@[path]
private lemma fkRectFullGraphEvent_to_indexed_eq
  {R : FKRectTorus}
  {B : Set R.Configuration}
  {rho : ConfigSpace (Sym2 R.Vertex)}
-- given
  (hrho : rho ∈ fkRectFullGraphEvent R B) :
-- imply
  fkRectIndexedConfigurationOfFullGraph R rho ∈ B := by
-- proof
  apply StatMech.FrontierD.fkRectFullGraphEvent_to_indexed R B hrho

/--
[fkRectInduced_openSub_indexedConfiguration_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedBarrierWindingMass.lean)
-/
@[path]
private lemma fkRectInduced_openSub_indexedConfiguration_eq_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {rho : ConfigSpace (Sym2 R.Vertex)} :
-- imply
  FK.openSub (fkRectInducedGraph R S) (FK.ocd_innerRestrict (Subtype.val : FKRectInducedVertex R S → R.Vertex) (fkRectFullGraphConfiguration R (fkRectIndexedConfigurationOfFullGraph R rho))) = FK.openSub (fkRectInducedGraph R S) (FK.ocd_innerRestrict (Subtype.val : FKRectInducedVertex R S → R.Vertex) rho) := by
-- proof
  apply StatMech.FrontierD.fkRectInduced_openSub_indexedConfiguration_eq R S rho

/--
[fkRectInduced_connectionChain_to_indexedConfiguration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedBarrierWindingMass.lean)
-/
@[path]
private lemma fkRectInduced_connectionChain_to_indexedConfiguration_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {t : Finset (FKRectInducedVertex R S × FKRectInducedVertex R S)}
-- given
  (hchain : FK.ocd_innerRestrict (Subtype.val : FKRectInducedVertex R S → R.Vertex) rho ∈ fkRectInducedConnectionChainEvent R S t) :
-- imply
  FK.ocd_innerRestrict (Subtype.val : FKRectInducedVertex R S → R.Vertex) (fkRectFullGraphConfiguration R (fkRectIndexedConfigurationOfFullGraph R rho)) ∈ fkRectInducedConnectionChainEvent R S t := by
-- proof
  apply StatMech.FrontierD.fkRectInduced_connectionChain_to_indexedConfiguration R S rho t hchain

/--
[fkRectAugmentedBarrierConnectionEvent_subset_fullGraphVerticalWinding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedBarrierWindingMass.lean)
-/
@[path]
private lemma fkRectAugmentedBarrierConnectionEvent_subset_fullGraphVerticalWinding_eq
  {R : FKRectTorus}
  {leftRight cut : Nat}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hgap : gap ∈ fkRectHorizontalCutEdges R)
  (hx : cut ≤ x.val)
  (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
  (hpair : (fkRectRightBandRowOne R cut x hx, fkRectRightBandLastRow R cut x hx) ∈ t) :
-- imply
  fkRectAugmentedBarrierConnectionEvent R leftRight cut gap x t ⊆ fkRectFullGraphEvent R (fkRectVerticalWindingEvent R) := by
-- proof
  apply StatMech.FrontierD.fkRectAugmentedBarrierConnectionEvent_subset_fullGraphVerticalWinding R leftRight cut hgap x hx hchosen t hpair

/--
[fkRectAugmentedBarrierConnectionEvent_subset_fullGraphSeparatedWinding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedBarrierWindingMass.lean)
-/
@[path]
private lemma fkRectAugmentedBarrierConnectionEvent_subset_fullGraphSeparatedWinding_eq
  {R : FKRectTorus}
  {leftRight cut : Nat}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hgap : gap ∈ fkRectHorizontalCutEdges R)
  (hx : cut ≤ x.val)
  (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
  (hpair : (fkRectRightBandRowOne R cut x hx, fkRectRightBandLastRow R cut x hx) ∈ t) :
-- imply
  fkRectAugmentedBarrierConnectionEvent R leftRight cut gap x t ⊆ fkRectFullGraphEvent R (fkRectSeparatedVerticalWindingEvent R leftRight) := by
-- proof
  apply StatMech.FrontierD.fkRectAugmentedBarrierConnectionEvent_subset_fullGraphSeparatedWinding R leftRight cut hgap x hx hchosen t hpair

/--
[fkRectAugmentedSource_barrierConnectionProduct_le_verticalWindingMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedBarrierWindingMass.lean)
-/
@[path]
private lemma fkRectAugmentedSource_barrierConnectionProduct_le_verticalWindingMass_eq
  {R : FKRectTorus}
  {leftRight cut : Nat}
  {q : Real}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hsep : leftRight < cut)
  (hq : 1 ≤ q)
  (hgap : gap ∈ fkRectHorizontalCutEdges R)
  (hx : cut ≤ x.val)
  (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
  (hpair : (fkRectRightBandRowOne R cut x hx, fkRectRightBandLastRow R cut x hx) ∈ t) :
-- imply
  (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2) * fkRectCriticalEventMass R q (fkRectAugmentedSourceBarrier R leftRight gap x) ≤ fkRectCriticalEventMass R q (fkRectVerticalWindingEvent R) := by
-- proof
  apply StatMech.FrontierD.fkRectAugmentedSource_barrierConnectionProduct_le_verticalWindingMass R leftRight cut hsep hq hgap x hx hchosen t hpair

/--
[fkRectAugmentedSource_barrierConnectionProduct_le_separatedWindingMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedBarrierWindingMass.lean)
-/
@[path]
private lemma fkRectAugmentedSource_barrierConnectionProduct_le_separatedWindingMass_eq
  {R : FKRectTorus}
  {leftRight cut : Nat}
  {q : Real}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hsep : leftRight < cut)
  (hq : 1 ≤ q)
  (hgap : gap ∈ fkRectHorizontalCutEdges R)
  (hx : cut ≤ x.val)
  (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
  (hpair : (fkRectRightBandRowOne R cut x hx, fkRectRightBandLastRow R cut x hx) ∈ t) :
-- imply
  (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2) * fkRectCriticalEventMass R q (fkRectAugmentedSourceBarrier R leftRight gap x) ≤ fkRectCriticalEventMass R q (fkRectSeparatedVerticalWindingEvent R leftRight) := by
-- proof
  apply StatMech.FrontierD.fkRectAugmentedSource_barrierConnectionProduct_le_separatedWindingMass R leftRight cut hsep hq hgap x hx hchosen t hpair


-- created on 2026-10-23
