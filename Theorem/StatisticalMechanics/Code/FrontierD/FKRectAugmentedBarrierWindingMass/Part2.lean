/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedBarrierWindingMass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedSourceBarrier.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierWindingMass.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectAugmentedBarrierConnectionEvent_subset_fullGraphSeparatedWinding
    (R : FKRectTorus) (leftRight cut : Nat)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut ≤ x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t) :
    fkRectAugmentedBarrierConnectionEvent R
        leftRight cut gap x t ⊆
      fkRectFullGraphEvent R
        (fkRectSeparatedVerticalWindingEvent R leftRight) := by
  intro rho hrho
  let omega := fkRectIndexedConfigurationOfFullGraph R rho
  have hbarrier : omega ∈
      fkRectAugmentedSourceBarrier R leftRight gap x :=
    fkRectFullGraphEvent_to_indexed R _ hrho.2
  have hwinding :=
    fkRectAugmentedBarrierConnectionEvent_subset_fullGraphVerticalWinding
      R leftRight cut hgap x hx hchosen t hpair hrho
  exact ⟨hbarrier.1, hwinding⟩


theorem fkRectAugmentedSource_barrierConnectionProduct_le_verticalWindingMass
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    {q : Real} (hq : 1 ≤ q)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut ≤ x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t) :
    (∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut 1 (R.height - 1)))
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q
          (fkRectAugmentedSourceBarrier R leftRight gap x) ≤
      fkRectCriticalEventMass R q (fkRectVerticalWindingEvent R) := by
  have hlower := fkRectAugmentedSource_barrierConnectionProduct_le
    R leftRight cut hsep hq gap x t
  apply hlower.trans
  rw [← fkRectFullGraphEvent_mass_eq R hq
    (fkRectVerticalWindingEvent R)]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hsource : rho ∈ fkRectAugmentedBarrierConnectionEvent R
      leftRight cut gap x t
  · have hwinding :=
      fkRectAugmentedBarrierConnectionEvent_subset_fullGraphVerticalWinding
        R leftRight cut hgap x hx hchosen t hpair hsource
    simp [Set.indicator_of_mem hsource, Set.indicator_of_mem hwinding]
  · by_cases hwinding : rho ∈
        fkRectFullGraphEvent R (fkRectVerticalWindingEvent R)
    · rw [Set.indicator_of_notMem hsource,
        Set.indicator_of_mem hwinding]
      have hq0 : (0 : Real) < q := zero_lt_one.trans_le hq
      simpa using
        (FK.fkProb_nonneg (G := fkRectTorusGraph R)
          (p := fkRectCriticalP q) (q := q)
          (fkRectCriticalP_pos hq0)
          (fkRectCriticalP_lt_one hq0) hq0 rho)
    · simp [Set.indicator_of_notMem hsource,
        Set.indicator_of_notMem hwinding]


theorem fkRectAugmentedSource_barrierConnectionProduct_le_separatedWindingMass
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    {q : Real} (hq : 1 ≤ q)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut ≤ x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t) :
    (∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut 1 (R.height - 1)))
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q
          (fkRectAugmentedSourceBarrier R leftRight gap x) ≤
      fkRectCriticalEventMass R q
        (fkRectSeparatedVerticalWindingEvent R leftRight) := by
  have hlower := fkRectAugmentedSource_barrierConnectionProduct_le
    R leftRight cut hsep hq gap x t
  apply hlower.trans
  rw [← fkRectFullGraphEvent_mass_eq R hq
    (fkRectSeparatedVerticalWindingEvent R leftRight)]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hsource : rho ∈ fkRectAugmentedBarrierConnectionEvent R
      leftRight cut gap x t
  · have htarget :=
      fkRectAugmentedBarrierConnectionEvent_subset_fullGraphSeparatedWinding
        R leftRight cut hgap x hx hchosen t hpair hsource
    simp [Set.indicator_of_mem hsource, Set.indicator_of_mem htarget]
  · by_cases htarget : rho ∈ fkRectFullGraphEvent R
        (fkRectSeparatedVerticalWindingEvent R leftRight)
    · rw [Set.indicator_of_notMem hsource,
        Set.indicator_of_mem htarget]
      have hq0 : (0 : Real) < q := zero_lt_one.trans_le hq
      simpa using
        (FK.fkProb_nonneg (G := fkRectTorusGraph R)
          (p := fkRectCriticalP q) (q := q)
          (fkRectCriticalP_pos hq0)
          (fkRectCriticalP_lt_one hq0) hq0 rho)
    · simp [Set.indicator_of_notMem hsource,
        Set.indicator_of_notMem htarget]

end
end StatMech.FrontierD
