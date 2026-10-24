import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectSourceChainWindingUpper
open SimpleGraph StatMech StatMech.FrontierD


/--
[connectionPathPairs_pair_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceChainWindingUpper.lean)
-/
@[path]
private lemma connectionPathPairs_pair_mem_eq
  [DecidableEq V]
  {n : Nat}
  {i : Fin n}
-- given
  (v : Fin (n + 1) -> V) :
-- imply
  (v i.castSucc, v i.succ) ∈ connectionPathPairs n v := by
-- proof
  apply StatMech.FrontierD.connectionPathPairs_pair_mem n v i

/--
[connectionPathPairs_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceChainWindingUpper.lean)
-/
@[path]
private lemma connectionPathPairs_card_le_eq
  [DecidableEq V]
  {n : Nat}
-- given
  (v : Fin (n + 1) -> V) :
-- imply
  (connectionPathPairs n v).card <= n := by
-- proof
  apply StatMech.FrontierD.connectionPathPairs_card_le n v

/--
[connectionPathPairs_card_eq_of_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceChainWindingUpper.lean)
-/
@[path]
private lemma connectionPathPairs_card_eq_of_injective_eq
  [DecidableEq V]
  {n : Nat}
-- given
  (v : Fin (n + 1) -> V)
  (hinj : Function.Injective (fun i : Fin n => (v i.castSucc, v i.succ))) :
-- imply
  (connectionPathPairs n v).card = n := by
-- proof
  apply StatMech.FrontierD.connectionPathPairs_card_eq_of_injective n v hinj

/--
[reachable_of_twoPointFun_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceChainWindingUpper.lean)
-/
@[path]
private lemma reachable_of_twoPointFun_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : Real}
  {x y : V}
-- given
  (hpos : 0 < FK.twoPointFun G p q x y) :
-- imply
  G.Reachable x y := by
-- proof
  apply StatMech.FrontierD.reachable_of_twoPointFun_pos G hpos

/--
[reachable_first_last_of_connectionPathPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceChainWindingUpper.lean)
-/
@[path]
private lemma reachable_first_last_of_connectionPathPairs_eq
  {G : SimpleGraph V} :
-- imply
  forall (n : Nat) (v : Fin (n + 1) -> V), (forall i : Fin n, G.Reachable (v i.castSucc) (v i.succ)) -> G.Reachable (v 0) (v (Fin.last n)) := by
-- proof
  apply StatMech.FrontierD.reachable_first_last_of_connectionPathPairs

/--
[fkRectRightBandConnectionChainSpans_connectionPathPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceChainWindingUpper.lean)
-/
@[path]
private lemma fkRectRightBandConnectionChainSpans_connectionPathPairs_eq
  {R : FKRectTorus}
  {cut : Nat}
  {x : Fin R.width}
  {n : Nat}
-- given
  (hx : cut <= x.val)
  (v : Fin (n + 1) -> FKRectRightStripBandVertex R cut 1 (R.height - 1))
  (hfirst : v 0 = fkRectRightBandRowOne R cut x hx)
  (hlast : v (Fin.last n) = fkRectRightBandLastRow R cut x hx) :
-- imply
  FKRectRightBandConnectionChainSpans R cut x hx (connectionPathPairs n v) := by
-- proof
  apply StatMech.FrontierD.fkRectRightBandConnectionChainSpans_connectionPathPairs R cut x hx n v hfirst hlast

/--
[fkRectRightBandConnectionChainSpans_of_pair_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceChainWindingUpper.lean)
-/
@[path]
private lemma fkRectRightBandConnectionChainSpans_of_pair_mem_eq
  {R : FKRectTorus}
  {cut : Nat}
  {x : Fin R.width}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hx : cut <= x.val)
  (hpair : (fkRectRightBandRowOne R cut x hx, fkRectRightBandLastRow R cut x hx) ∈ t) :
-- imply
  FKRectRightBandConnectionChainSpans R cut x hx t := by
-- proof
  apply StatMech.FrontierD.fkRectRightBandConnectionChainSpans_of_pair_mem R cut x hx t hpair

/--
[fkRectVerticalWindingEvent_of_rightBand_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceChainWindingUpper.lean)
-/
@[path]
private lemma fkRectVerticalWindingEvent_of_rightBand_reachable_eq
  {R : FKRectTorus}
  {x : Fin R.width}
  {omega : R.Configuration}
-- given
  (hband : (fkRectVerticalCutGraph R omega).Reachable (fkRectRowOneVertex R x) (fkRectLastRowVertex R x))
  (hseam : omega (fkRectVerticalSeamEdgeAt R x) = true)
  (hattach : omega (fkRectRowZeroAttachmentEdgeAt R x) = true) :
-- imply
  omega ∈ fkRectVerticalWindingEvent R := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalWindingEvent_of_rightBand_reachable R x omega hband hseam hattach

/--
[fkRectAugmentedBarrierConnectionEvent_subset_fullGraphVerticalWinding_of_spans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceChainWindingUpper.lean)
-/
@[path]
private lemma fkRectAugmentedBarrierConnectionEvent_subset_fullGraphVerticalWinding_of_spans_eq
  {R : FKRectTorus}
  {leftRight cut : Nat}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hgap : gap ∈ fkRectHorizontalCutEdges R)
  (hx : cut <= x.val)
  (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
  (hspans : FKRectRightBandConnectionChainSpans R cut x hx t) :
-- imply
  fkRectAugmentedBarrierConnectionEvent R leftRight cut gap x t ⊆ fkRectFullGraphEvent R (fkRectVerticalWindingEvent R) := by
-- proof
  apply StatMech.FrontierD.fkRectAugmentedBarrierConnectionEvent_subset_fullGraphVerticalWinding_of_spans R leftRight cut hgap x hx hchosen t hspans

/--
[fkRectAugmentedBarrierConnectionEvent_subset_fullGraphWindingOne_of_spans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceChainWindingUpper.lean)
-/
@[path]
private lemma fkRectAugmentedBarrierConnectionEvent_subset_fullGraphWindingOne_of_spans_eq
  {R : FKRectTorus}
  {leftRight cut : Nat}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hleft : leftRight + 1 < R.width)
  (hgap : gap ∈ fkRectHorizontalCutEdges R)
  (hx : cut <= x.val)
  (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
  (hspans : FKRectRightBandConnectionChainSpans R cut x hx t) :
-- imply
  fkRectAugmentedBarrierConnectionEvent R leftRight cut gap x t ⊆ fkRectFullGraphEvent R {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} := by
-- proof
  apply StatMech.FrontierD.fkRectAugmentedBarrierConnectionEvent_subset_fullGraphWindingOne_of_spans R leftRight cut hleft hgap x hx hchosen t hspans

/--
[fkRectAugmentedSource_barrierConnectionProduct_le_windingOneMass_of_spans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceChainWindingUpper.lean)
-/
@[path]
private lemma fkRectAugmentedSource_barrierConnectionProduct_le_windingOneMass_of_spans_eq
  {R : FKRectTorus}
  {leftRight cut : Nat}
  {q : Real}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hsep : leftRight < cut)
  (hleft : leftRight + 1 < R.width)
  (hq : 1 <= q)
  (hgap : gap ∈ fkRectHorizontalCutEdges R)
  (hx : cut <= x.val)
  (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
  (hspans : FKRectRightBandConnectionChainSpans R cut x hx t) :
-- imply
  (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2) * fkRectCriticalEventMass R q (fkRectAugmentedSourceBarrier R leftRight gap x) <= fkRectCriticalEventMass R q {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} := by
-- proof
  apply StatMech.FrontierD.fkRectAugmentedSource_barrierConnectionProduct_le_windingOneMass_of_spans R leftRight cut hsep hleft hq hgap x hx hchosen t hspans

/--
[fkRectSource_barrierConnectionProduct_le_windingOneMass_of_spans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceChainWindingUpper.lean)
-/
@[path]
private lemma fkRectSource_barrierConnectionProduct_le_windingOneMass_of_spans_eq
  {R : FKRectTorus}
  {leftRight cut : Nat}
  {q : Real}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hsep : leftRight < cut)
  (hleft : leftRight + 1 < R.width)
  (hq : 1 <= q)
  (hgap : gap ∈ fkRectHorizontalCutEdges R)
  (hx : cut <= x.val)
  (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
  (hspans : FKRectRightBandConnectionChainSpans R cut x hx t) :
-- imply
  FK.cFE (fkRectCriticalP q) q * (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2) * fkRectCriticalEventMass R q (fkRectSourceLeftBarrier R leftRight gap) <= fkRectCriticalEventMass R q {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} := by
-- proof
  apply StatMech.FrontierD.fkRectSource_barrierConnectionProduct_le_windingOneMass_of_spans R leftRight cut hsep hleft hq hgap x hx hchosen t hspans


-- created on 2026-10-23
