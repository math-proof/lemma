/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceChainWindingUpper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamWindingUpper.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectSourceChainWindingUpper.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRightBandConnectionChainSpans_connectionPathPairs
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width)
    (hx : cut <= x.val) (n : Nat)
    (v : Fin (n + 1) ->
      FKRectRightStripBandVertex R cut 1 (R.height - 1))
    (hfirst : v 0 = fkRectRightBandRowOne R cut x hx)
    (hlast : v (Fin.last n) = fkRectRightBandLastRow R cut x hx) :
    FKRectRightBandConnectionChainSpans R cut x hx
      (connectionPathPairs n v) := by
  intro sigma hchain
  rw [← hfirst, ← hlast]
  apply reachable_first_last_of_connectionPathPairs n v
  intro i
  exact hchain _ (connectionPathPairs_pair_mem n v i)

theorem fkRectRightBandConnectionChainSpans_of_pair_mem
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width)
    (hx : cut <= x.val)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t) :
    FKRectRightBandConnectionChainSpans R cut x hx t := by
  intro sigma hchain
  exact hchain _ hpair


theorem fkRectVerticalWindingEvent_of_rightBand_reachable
    (R : FKRectTorus) (x : Fin R.width) (omega : R.Configuration)
    (hband : (fkRectVerticalCutGraph R omega).Reachable
      (fkRectRowOneVertex R x) (fkRectLastRowVertex R x))
    (hseam : omega (fkRectVerticalSeamEdgeAt R x) = true)
    (hattach : omega (fkRectRowZeroAttachmentEdgeAt R x) = true) :
    omega ∈ fkRectVerticalWindingEvent R := by
  let v0 := fkRectRowZeroVertex R x
  let v1 := fkRectRowOneVertex R x
  let vt := fkRectLastRowVertex R x
  have hseamAdj : (fkRectOpenGraph R omega).Adj v0 vt := by
    refine ⟨fkRectVerticalSeamEdgeAt R x, hseam, ?_⟩
    exact fkRectVerticalSeamEdgeAt_indexedEdge R x
  have hattachAdj : (fkRectVerticalCutGraph R omega).Adj v0 v1 := by
    rw [fkRectVerticalCutGraph, SimpleGraph.deleteEdges_adj]
    constructor
    · refine ⟨fkRectRowZeroAttachmentEdgeAt R x, hattach, ?_⟩
      rw [fkRectRowZeroAttachmentEdgeAt_indexedEdge]
      exact Sym2.eq_swap
    · intro hcross
      apply fkRectRowZeroAttachmentEdgeAt_not_crosses R x
      rw [fkRectRowZeroAttachmentEdgeAt_indexedEdge]
      simpa only [Sym2.eq_swap] using hcross
  refine ⟨v0, vt, hseamAdj, ?_, hattachAdj.reachable.trans hband⟩
  rw [← fkRectVerticalSeamEdgeAt_indexedEdge R x]
  exact fkRectVerticalSeamEdgeAt_crosses R x


theorem fkRectAugmentedBarrierConnectionEvent_subset_fullGraphVerticalWinding_of_spans
    (R : FKRectTorus) (leftRight cut : Nat)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut <= x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hspans : FKRectRightBandConnectionChainSpans R cut x hx t) :
    fkRectAugmentedBarrierConnectionEvent R leftRight cut gap x t ⊆
      fkRectFullGraphEvent R (fkRectVerticalWindingEvent R) := by
  intro rho hrho
  let omega := fkRectIndexedConfigurationOfFullGraph R rho
  have hbarrier : omega ∈
      fkRectAugmentedSourceBarrier R leftRight gap x :=
    fkRectFullGraphEvent_to_indexed R _ hrho.2
  have hreachRho := hspans _ hrho.1
  have hreach :
      (FK.openSub
        (fkRectInducedGraph R
          (fkRectRightStripBand R cut 1 (R.height - 1)))
        (FK.ocd_innerRestrict
          (Subtype.val :
            FKRectRightStripBandVertex R cut 1 (R.height - 1) -> R.Vertex)
          (fkRectFullGraphConfiguration R omega))).Reachable
        (fkRectRightBandRowOne R cut x hx)
        (fkRectRightBandLastRow R cut x hx) := by
    rw [fkRectInduced_openSub_indexedConfiguration_eq R
      (fkRectRightStripBand R cut 1 (R.height - 1)) rho]
    exact hreachRho
  have hband := fkRectRightStripBand_connection_reachable_verticalCut
    R cut 1 (R.height - 1) (by omega) omega
      (fkRectRightBandRowOne R cut x hx)
      (fkRectRightBandLastRow R cut x hx) hreach
  have hopen := fkRectAugmentedSourceBarrier_witnessEdges_open
    R leftRight hgap x hchosen hbarrier
  change omega ∈ fkRectVerticalWindingEvent R
  exact fkRectVerticalWindingEvent_of_rightBand_reachable
    R x omega hband hopen.1 hopen.2


theorem fkRectAugmentedBarrierConnectionEvent_subset_fullGraphWindingOne_of_spans
    (R : FKRectTorus) (leftRight cut : Nat)
    (hleft : leftRight + 1 < R.width)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut <= x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hspans : FKRectRightBandConnectionChainSpans R cut x hx t) :
    fkRectAugmentedBarrierConnectionEvent R leftRight cut gap x t ⊆
      fkRectFullGraphEvent R
        {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} := by
  intro rho hrho
  let omega := fkRectIndexedConfigurationOfFullGraph R rho
  have hbarrier : omega ∈
      fkRectAugmentedSourceBarrier R leftRight gap x :=
    fkRectFullGraphEvent_to_indexed R _ hrho.2
  have hwinding : omega ∈ fkRectVerticalWindingEvent R :=
    fkRectFullGraphEvent_to_indexed R _
      (fkRectAugmentedBarrierConnectionEvent_subset_fullGraphVerticalWinding_of_spans
        R leftRight cut hgap x hx hchosen t hspans hrho)
  have hseparated : omega ∈
      fkRectSeparatedVerticalWindingEvent R leftRight :=
    ⟨hbarrier.1, hwinding⟩
  have hrank : omega ∈ fkRectVerticalRankOneEvent R :=
    fkRectSeparatedVerticalWindingEvent_subset_verticalRankOne
      R leftRight hleft hseparated
  have hlower : 1 <= fkRectUnorientedVerticalWindingNumber R omega :=
    fkRectVerticalRankOneEvent_subset_windingTail R hrank
  have hupper : fkRectUnorientedVerticalWindingNumber R omega <= 1 :=
    fkRectUnorientedVerticalWindingNumber_le_one_of_allButOneOpenSeam
      R (fkRectAugmentedSourceBarrier_subset_allButOneOpenSeamEvent
        R leftRight gap x hbarrier)
  exact le_antisymm hupper hlower


theorem fkRectAugmentedSource_barrierConnectionProduct_le_windingOneMass_of_spans
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < R.width)
    {q : Real} (hq : 1 <= q)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut <= x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hspans : FKRectRightBandConnectionChainSpans R cut x hx t) :
    (∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut 1 (R.height - 1)))
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q
          (fkRectAugmentedSourceBarrier R leftRight gap x) <=
      fkRectCriticalEventMass R q
        {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} := by
  have hlower := fkRectAugmentedSource_barrierConnectionProduct_le
    R leftRight cut hsep hq gap x t
  apply hlower.trans
  rw [← fkRectFullGraphEvent_mass_eq R hq
    {omega | fkRectUnorientedVerticalWindingNumber R omega = 1}]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hsource : rho ∈ fkRectAugmentedBarrierConnectionEvent R
      leftRight cut gap x t
  · have htarget :=
      fkRectAugmentedBarrierConnectionEvent_subset_fullGraphWindingOne_of_spans
        R leftRight cut hleft hgap x hx hchosen t hspans hsource
    simp [Set.indicator_of_mem hsource, Set.indicator_of_mem htarget]
  · by_cases htarget : rho ∈ fkRectFullGraphEvent R
        {omega | fkRectUnorientedVerticalWindingNumber R omega = 1}
    · rw [Set.indicator_of_notMem hsource, Set.indicator_of_mem htarget]
      have hq0 : (0 : Real) < q := zero_lt_one.trans_le hq
      simpa using
        (FK.fkProb_nonneg (G := fkRectTorusGraph R)
          (p := fkRectCriticalP q) (q := q)
          (fkRectCriticalP_pos hq0)
          (fkRectCriticalP_lt_one hq0) hq0 rho)
    · simp [Set.indicator_of_notMem hsource,
        Set.indicator_of_notMem htarget]


theorem fkRectSource_barrierConnectionProduct_le_windingOneMass_of_spans
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < R.width)
    {q : Real} (hq : 1 <= q)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut <= x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hspans : FKRectRightBandConnectionChainSpans R cut x hx t) :
    FK.cFE (fkRectCriticalP q) q *
        (∏ xy ∈ t,
          FK.twoPointFun
            (fkRectInducedGraph R
              (fkRectRightStripBand R cut 1 (R.height - 1)))
            (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q
          (fkRectSourceLeftBarrier R leftRight gap) <=
      fkRectCriticalEventMass R q
        {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} := by
  let P : Real := ∏ xy ∈ t,
    FK.twoPointFun
      (fkRectInducedGraph R
        (fkRectRightStripBand R cut 1 (R.height - 1)))
      (fkRectCriticalP q) q xy.1 xy.2
  have hP : 0 <= P := by
    apply Finset.prod_nonneg
    intro xy hxy
    exact FK.twoPointFun_nonneg
      (fkRectInducedGraph R
        (fkRectRightStripBand R cut 1 (R.height - 1)))
      (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
      (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq))
      (zero_lt_one.trans_le hq) xy.1 xy.2
  calc
    FK.cFE (fkRectCriticalP q) q * P *
        fkRectCriticalEventMass R q
          (fkRectSourceLeftBarrier R leftRight gap) =
      P * (FK.cFE (fkRectCriticalP q) q *
        fkRectCriticalEventMass R q
          (fkRectSourceLeftBarrier R leftRight gap)) := by ring
    _ <= P * fkRectCriticalEventMass R q
        (fkRectAugmentedSourceBarrier R leftRight gap x) :=
      mul_le_mul_of_nonneg_left
        (fkRectCritical_cFE_mul_sourceBarrier_le_augmentedSourceBarrier
          R leftRight gap x (by omega) hq) hP
    _ <= fkRectCriticalEventMass R q
        {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} :=
      fkRectAugmentedSource_barrierConnectionProduct_le_windingOneMass_of_spans
        R leftRight cut hsep hleft hq hgap x hx hchosen t hspans

end
end StatMech.FrontierD
