/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRankOneWindingTail
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryVerticalFlux.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierPatternCost
import Def.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamWindingUpper.Part3
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkMedialLoopCanonicalVerticalFlux_eq_sum_cutColumns
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)) :
    fkMedialLoopCanonicalVerticalFlux
        (fkRectConfigurationToMedialPairing R omega) C =
      ∑ x : Fin R.width,
        (fkRectMedialLoopCutColumnContribution R omega C x false +
          fkRectMedialLoopCutColumnContribution R omega C x true) := by
  classical
  unfold fkMedialLoopCanonicalVerticalFlux
  calc
    (∑ i : Fin R.medialTorus.width,
      if (fkMedialLoopGraph R.medialTorus
            (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
              (fkMedialVerticalSeamDart R.medialTorus i) = C then
        fkMedialCanonicalVerticalSeamSign R.medialTorus i else 0) =
      ∑ xb : Fin R.width × Bool,
        fkRectMedialLoopCutColumnContribution R omega C xb.1 xb.2 := by
      apply Fintype.sum_equiv (fkRectCutMedialColumnEquiv R).symm
      intro i
      unfold fkRectMedialLoopCutColumnContribution
      have hcol : fkRectCutMedialColumn R
          ((fkRectCutMedialColumnEquiv R).symm i).1
          ((fkRectCutMedialColumnEquiv R).symm i).2 = i := by
        simpa [fkRectCutMedialColumnEquiv] using
          (fkRectCutMedialColumnEquiv R).apply_symm_apply i
      rw [hcol]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Fintype.sum_bool]
      ac_rfl


theorem fkRectAllButOneOpenSeamEvent_both_open_of_column_ne
    (R : FKRectTorus) {gap : R.EdgeIndex}
    {omega : R.Configuration}
    (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap)
    {x : Fin R.width} (hx : x ≠ gap.2.1) :
    omega (false, (x, ⟨0, R.height_pos⟩)) = true ∧
      omega (true, (x, ⟨0, R.height_pos⟩)) = true := by
  have edge_ne (b : Bool) : (b, (x, ⟨0, R.height_pos⟩)) ≠ gap := by
    intro h
    apply hx
    exact congrArg (fun e : R.EdgeIndex => e.2.1) h
  constructor
  · exact (fkRectAllButOneOpenSeamEvent_open_iff R
      (homega := homega) (a := (false, (x, ⟨0, R.height_pos⟩)))
      (by simp [mem_fkRectHorizontalCutEdges_iff])).2 (edge_ne false)
  · exact (fkRectAllButOneOpenSeamEvent_open_iff R
      (homega := homega) (a := (true, (x, ⟨0, R.height_pos⟩)))
      (by simp [mem_fkRectHorizontalCutEdges_iff])).2 (edge_ne true)


theorem fkRectMedialLoopCutColumnContribution_add_eq_zero_of_ne_gap
    (R : FKRectTorus) {gap : R.EdgeIndex}
    {omega : R.Configuration}
    (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega))
    {x : Fin R.width} (hx : x ≠ gap.2.1) :
    fkRectMedialLoopCutColumnContribution R omega C x false +
      fkRectMedialLoopCutColumnContribution R omega C x true = 0 := by
  classical
  obtain ⟨hfalse, htrue⟩ :=
    fkRectAllButOneOpenSeamEvent_both_open_of_column_ne
      R homega hx
  have hcomponent := fkRectCutMedialColumns_component_eq_of_both_open
    R omega x hfalse htrue
  unfold fkRectMedialLoopCutColumnContribution
  by_cases hC :
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkMedialVerticalSeamDart R.medialTorus
            (fkRectCutMedialColumn R x false)) = C
  · rw [if_pos hC, if_pos (hcomponent ▸ hC)]
    exact fkRectCutMedialColumn_canonicalVerticalSeamSign_add R x
  · have hC' :
        (fkMedialLoopGraph R.medialTorus
          (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
            (fkMedialVerticalSeamDart R.medialTorus
              (fkRectCutMedialColumn R x true)) ≠ C := by
      rwa [← hcomponent]
    simp [hC, hC']


theorem fkMedialLoopCanonicalVerticalFlux_eq_gapColumn
    (R : FKRectTorus) {gap : R.EdgeIndex}
    {omega : R.Configuration}
    (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)) :
    fkMedialLoopCanonicalVerticalFlux
        (fkRectConfigurationToMedialPairing R omega) C =
      fkRectMedialLoopCutColumnContribution R omega C gap.2.1 false +
        fkRectMedialLoopCutColumnContribution R omega C gap.2.1 true := by
  rw [fkMedialLoopCanonicalVerticalFlux_eq_sum_cutColumns]
  classical
  rw [Finset.sum_eq_single gap.2.1]
  · intro x hx hne
    exact fkRectMedialLoopCutColumnContribution_add_eq_zero_of_ne_gap
      R homega C hne
  · simp


theorem sum_natAbs_fkRectMedialLoopCutColumnContribution_eq_one
    (R : FKRectTorus) (omega : R.Configuration)
    (x : Fin R.width) (b : Bool) :
    ∑ C : FKMedialLoop R.medialTorus
        (fkRectConfigurationToMedialPairing R omega),
      (fkRectMedialLoopCutColumnContribution R omega C x b).natAbs = 1 := by
  classical
  let C0 := (fkMedialLoopGraph R.medialTorus
    (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
      (fkMedialVerticalSeamDart R.medialTorus
        (fkRectCutMedialColumn R x b))
  rw [Finset.sum_eq_single C0]
  · unfold fkRectMedialLoopCutColumnContribution
    rw [if_pos rfl]
    unfold fkMedialCanonicalVerticalSeamSign
    split <;> simp
  · intro C hC hne
    unfold fkRectMedialLoopCutColumnContribution
    rw [if_neg]
    · rfl
    · exact hne.symm
  · simp


theorem fkMedialUnorientedVerticalWindingTotal_le_two_of_allButOneOpenSeam
    (R : FKRectTorus) {gap : R.EdgeIndex}
    {omega : R.Configuration}
    (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap) :
    fkMedialUnorientedVerticalWindingTotal
        (fkRectConfigurationToMedialPairing R omega) ≤ 2 := by
  classical
  unfold fkMedialUnorientedVerticalWindingTotal
  calc
    (∑ C : FKMedialLoop R.medialTorus
        (fkRectConfigurationToMedialPairing R omega),
      (fkMedialLoopCanonicalVerticalFlux
        (fkRectConfigurationToMedialPairing R omega) C).natAbs) =
      ∑ C : FKMedialLoop R.medialTorus
          (fkRectConfigurationToMedialPairing R omega),
        (fkRectMedialLoopCutColumnContribution R omega C gap.2.1 false +
          fkRectMedialLoopCutColumnContribution R omega C gap.2.1 true).natAbs := by
      apply Finset.sum_congr rfl
      intro C hC
      rw [fkMedialLoopCanonicalVerticalFlux_eq_gapColumn
        R homega C]
    _ ≤ ∑ C : FKMedialLoop R.medialTorus
          (fkRectConfigurationToMedialPairing R omega),
        ((fkRectMedialLoopCutColumnContribution R omega C gap.2.1 false).natAbs +
          (fkRectMedialLoopCutColumnContribution R omega C gap.2.1 true).natAbs) := by
      apply Finset.sum_le_sum
      intro C hC
      exact Int.natAbs_add_le _ _
    _ = 2 := by
      rw [Finset.sum_add_distrib,
        sum_natAbs_fkRectMedialLoopCutColumnContribution_eq_one,
        sum_natAbs_fkRectMedialLoopCutColumnContribution_eq_one]


theorem fkRectUnorientedVerticalWindingNumber_le_one_of_allButOneOpenSeam
    (R : FKRectTorus) {gap : R.EdgeIndex}
    {omega : R.Configuration}
    (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap) :
    fkRectUnorientedVerticalWindingNumber R omega ≤ 1 := by
  unfold fkRectUnorientedVerticalWindingNumber
    fkRectUnorientedVerticalWindingTotal
  have h :=
    fkMedialUnorientedVerticalWindingTotal_le_two_of_allButOneOpenSeam
      R homega
  omega


theorem fkRectAugmentedSourceBarrier_subset_allButOneOpenSeamEvent
    (R : FKRectTorus) (leftRight : Nat) (gap : R.EdgeIndex)
    (x : Fin R.width) :
    fkRectAugmentedSourceBarrier R leftRight gap x ⊆
      fkRectAllButOneOpenSeamEvent R gap := by
  intro omega homega a ha
  exact homega.2 a (Finset.mem_union_left _ ha)


theorem fkRectAugmentedBarrierConnectionEvent_subset_fullGraphWindingOne
    (R : FKRectTorus) (leftRight cut : Nat)
    (hleft : leftRight + 1 < R.width)
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
        {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} := by
  intro rho hrho
  let omega := fkRectIndexedConfigurationOfFullGraph R rho
  have hbarrier : omega ∈
      fkRectAugmentedSourceBarrier R leftRight gap x :=
    fkRectFullGraphEvent_to_indexed R _ hrho.2
  have hseparated : omega ∈
      fkRectSeparatedVerticalWindingEvent R leftRight :=
    fkRectFullGraphEvent_to_indexed R _
      (fkRectAugmentedBarrierConnectionEvent_subset_fullGraphSeparatedWinding
        R leftRight cut hgap x hx hchosen t hpair hrho)
  have hrank : omega ∈ fkRectVerticalRankOneEvent R :=
    fkRectSeparatedVerticalWindingEvent_subset_verticalRankOne
      R leftRight hleft hseparated
  have hlower : 1 ≤ fkRectUnorientedVerticalWindingNumber R omega :=
    fkRectVerticalRankOneEvent_subset_windingTail R hrank
  have hupper : fkRectUnorientedVerticalWindingNumber R omega ≤ 1 :=
    fkRectUnorientedVerticalWindingNumber_le_one_of_allButOneOpenSeam
      R (fkRectAugmentedSourceBarrier_subset_allButOneOpenSeamEvent
        R leftRight gap x hbarrier)
  exact le_antisymm hupper hlower


theorem fkRectAugmentedSource_barrierConnectionProduct_le_windingOneMass
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < R.width)
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
      fkRectAugmentedBarrierConnectionEvent_subset_fullGraphWindingOne
        R leftRight cut hleft hgap x hx hchosen t hpair hsource
    simp [Set.indicator_of_mem hsource, Set.indicator_of_mem htarget]
  · by_cases htarget : rho ∈ fkRectFullGraphEvent R
        {omega | fkRectUnorientedVerticalWindingNumber R omega = 1}
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


theorem fkRectSource_barrierConnectionProduct_le_windingOneMass
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < R.width)
    {q : Real} (hq : 1 ≤ q)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut ≤ x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t) :
    FK.cFE (fkRectCriticalP q) q *
        (∏ xy ∈ t,
          FK.twoPointFun
            (fkRectInducedGraph R
              (fkRectRightStripBand R cut 1 (R.height - 1)))
            (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q
          (fkRectSourceLeftBarrier R leftRight gap) ≤
      fkRectCriticalEventMass R q
        {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} := by
  let P : Real := ∏ xy ∈ t,
    FK.twoPointFun
      (fkRectInducedGraph R
        (fkRectRightStripBand R cut 1 (R.height - 1)))
      (fkRectCriticalP q) q xy.1 xy.2
  have hP : 0 ≤ P := by
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
    _ ≤ P * fkRectCriticalEventMass R q
        (fkRectAugmentedSourceBarrier R leftRight gap x) :=
      mul_le_mul_of_nonneg_left
        (fkRectCritical_cFE_mul_sourceBarrier_le_augmentedSourceBarrier
          R leftRight gap x (by omega) hq) hP
    _ ≤ fkRectCriticalEventMass R q
        {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} :=
      fkRectAugmentedSource_barrierConnectionProduct_le_windingOneMass
        R leftRight cut hsep hleft hq hgap x hx hchosen t hpair

end
end StatMech.FrontierD
