/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamPatternPreservation.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierWindingMass.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierAuxiliary.Part4


namespace StatMech.FrontierD

noncomputable section

theorem fkRectUnitAttachmentOpenEvent_dependsOnOutsideColumnBand
    (R : FKRectTorus) (left right lower upper : Nat)
    (hlower : 1 <= lower) :
    FKRectDependsOnOutsideRegion R
      (fkRectColumnBand R left right lower upper)
      (fkRectUnitAttachmentOpenEvent R) := by
  intro omega tau hot
  have hout : fkRectTorusIndexedEdge R
        (fkRectRowZeroAttachmentEdgeAt R (fkRectUnitGapColumn R)) ∉
      Set.range (FK.ocd_innerEdge
        (Subtype.val :
          FKRectColumnBandVertex R left right lower upper -> R.Vertex)) := by
    rw [fkRectRowZeroAttachmentEdgeAt_indexedEdge,
      fkRect_innerEdge_subtype_mk_mem_range_iff]
    intro hboth
    have hzero := hboth.2.2.2.1
    change lower <= 0 at hzero
    omega
  change omega (fkRectRowZeroAttachmentEdgeAt R
      (fkRectUnitGapColumn R)) = true ↔
    tau (fkRectRowZeroAttachmentEdgeAt R
      (fkRectUnitGapColumn R)) = true
  rw [hot _ hout]

theorem fkRectUnitAttachmentOpenEvent_mass_pos
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    0 < fkRectCriticalEventMass R q
      (fkRectUnitAttachmentOpenEvent R) := by
  exact fkRectCriticalEventMass_pos_of_mem R hq _
    (fun _ => true) rfl


theorem fkRectColumnBand_genericInter_subset_fullGraphAuxiliary
    (R : FKRectTorus) (right : Nat)
    (t : Finset
      (FKRectColumnBandVertex R 1 right 1 (R.height - 1) ×
        FKRectColumnBandVertex R 1 right 1 (R.height - 1))) :
    (FK.ocd_innerRestrict
        (Subtype.val :
          FKRectColumnBandVertex R 1 right 1 (R.height - 1) -> R.Vertex) ⁻¹'
        fkRectInducedConnectionChainEvent R
          (fkRectColumnBand R 1 right 1 (R.height - 1)) t) ∩
      fkRectFullGraphEvent R (fkRectUnitAttachmentOpenEvent R) ⊆
        fkRectFullGraphEvent R (fkRectUnitDualBarrierAuxiliary R right t) := by
  intro rho hrho
  let omega := fkRectIndexedConfigurationOfFullGraph R rho
  have hchain :
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectColumnBandVertex R 1 right 1 (R.height - 1) -> R.Vertex)
          (fkRectFullGraphConfiguration R omega) ∈
        fkRectInducedConnectionChainEvent R
          (fkRectColumnBand R 1 right 1 (R.height - 1)) t := by
    exact fkRectInduced_connectionChain_to_indexedConfiguration R
      (fkRectColumnBand R 1 right 1 (R.height - 1)) rho t hrho.1
  have hattach : omega ∈ fkRectUnitAttachmentOpenEvent R :=
    fkRectFullGraphEvent_to_indexed R _ hrho.2
  change omega ∈ fkRectUnitDualBarrierAuxiliary R right t
  exact ⟨hchain, hattach⟩


theorem fkRectColumnBand_connectionProduct_mul_attachment_le_auxiliary
    (R : FKRectTorus) (right : Nat) {q : Real} (hq : 1 <= q)
    (t : Finset
      (FKRectColumnBandVertex R 1 right 1 (R.height - 1) ×
        FKRectColumnBandVertex R 1 right 1 (R.height - 1))) :
    (∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R
            (fkRectColumnBand R 1 right 1 (R.height - 1)))
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q (fkRectUnitAttachmentOpenEvent R) <=
      fkRectCriticalEventMass R q
        (fkRectUnitDualBarrierAuxiliary R right t) := by
  have hlower :=
    fkRectInduced_connectionProduct_mul_outsideMass_le_genericInter
      R (fkRectColumnBand R 1 right 1 (R.height - 1)) hq t
      (fkRectUnitAttachmentOpenEvent_dependsOnOutsideColumnBand
        R 1 right 1 (R.height - 1) (by rfl))
  apply hlower.trans
  rw [← fkRectFullGraphEvent_mass_eq R hq
    (fkRectUnitDualBarrierAuxiliary R right t)]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hsource : rho ∈
      (FK.ocd_innerRestrict
          (Subtype.val :
            FKRectColumnBandVertex R 1 right 1 (R.height - 1) -> R.Vertex) ⁻¹'
        fkRectInducedConnectionChainEvent R
          (fkRectColumnBand R 1 right 1 (R.height - 1)) t) ∩
        fkRectFullGraphEvent R (fkRectUnitAttachmentOpenEvent R)
  · have htarget :=
      fkRectColumnBand_genericInter_subset_fullGraphAuxiliary
        R right t hsource
    simp [Set.indicator_of_mem hsource, Set.indicator_of_mem htarget]
  · by_cases htarget : rho ∈ fkRectFullGraphEvent R
        (fkRectUnitDualBarrierAuxiliary R right t)
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


theorem fkRectColumnBand_attachment_mul_pow_le_auxiliary
    (R : FKRectTorus) (right blocks : Nat)
    {q a : Real} (hq : 1 <= q) (ha : 0 < a) (ha1 : a <= 1)
    (t : Finset
      (FKRectColumnBandVertex R 1 right 1 (R.height - 1) ×
        FKRectColumnBandVertex R 1 right 1 (R.height - 1)))
    (hcard : t.card <= blocks)
    (hlower : ∀ xy ∈ t, a <=
      FK.twoPointFun
        (fkRectInducedGraph R
          (fkRectColumnBand R 1 right 1 (R.height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2) :
    fkRectCriticalEventMass R q (fkRectUnitAttachmentOpenEvent R) *
        a ^ blocks <=
      fkRectCriticalEventMass R q
        (fkRectUnitDualBarrierAuxiliary R right t) := by
  have hprod : a ^ t.card <=
      ∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R
            (fkRectColumnBand R 1 right 1 (R.height - 1)))
          (fkRectCriticalP q) q xy.1 xy.2 := by
    rw [show a ^ t.card = ∏ _xy ∈ t, a by simp]
    exact Finset.prod_le_prod (fun _ _ => ha.le) hlower
  have hpow : a ^ blocks <= a ^ t.card :=
    pow_le_pow_of_le_one ha.le ha1 hcard
  have hmassNonneg := fkRectCriticalEventMass_nonneg R
    (zero_lt_one.trans_le hq) (fkRectUnitAttachmentOpenEvent R)
  calc
    fkRectCriticalEventMass R q (fkRectUnitAttachmentOpenEvent R) *
        a ^ blocks <=
      fkRectCriticalEventMass R q (fkRectUnitAttachmentOpenEvent R) *
        (∏ xy ∈ t,
          FK.twoPointFun
            (fkRectInducedGraph R
              (fkRectColumnBand R 1 right 1 (R.height - 1)))
            (fkRectCriticalP q) q xy.1 xy.2) :=
      mul_le_mul_of_nonneg_left (hpow.trans hprod) hmassNonneg
    _ = (∏ xy ∈ t,
          FK.twoPointFun
            (fkRectInducedGraph R
              (fkRectColumnBand R 1 right 1 (R.height - 1)))
            (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q (fkRectUnitAttachmentOpenEvent R) := by
      ring
    _ <= _ := fkRectColumnBand_connectionProduct_mul_attachment_le_auxiliary
      R right hq t


theorem fkRectForceDualPullbackSeam_preserves_columnBand_chain
    (R : FKRectTorus) (left right lower upper : Nat)
    (hlower : 1 <= lower) (eta omega : R.Configuration)
    (t : Finset
      (FKRectColumnBandVertex R left right lower upper ×
        FKRectColumnBandVertex R left right lower upper))
    (hchain :
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectColumnBandVertex R left right lower upper -> R.Vertex)
          (fkRectFullGraphConfiguration R omega) ∈
        fkRectInducedConnectionChainEvent R
          (fkRectColumnBand R left right lower upper) t) :
    FK.ocd_innerRestrict
        (Subtype.val :
          FKRectColumnBandVertex R left right lower upper -> R.Vertex)
        (fkRectFullGraphConfiguration R
          (fkRectForceIndexedPattern R
            (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
            eta omega)) ∈
      fkRectInducedConnectionChainEvent R
        (fkRectColumnBand R left right lower upper) t := by
  rw [fkRectDualPullbackIndexSet_horizontalCutEdges]
  have heq := fkRectForceIndexedPattern_innerRestrict_eq_of_outside
    R (fkRectColumnBand R left right lower upper)
      (fkRectHorizontalCutEdges R) eta omega
      (by
        intro a ha
        exact fkRect_verticalSeam_not_innerEdgeRange_of_rowZero_disjoint
          R (fkRectColumnBand R left right lower upper)
            (by
              intro v hv
              exact Nat.ne_of_gt (Nat.zero_lt_one.trans_le
                (hlower.trans hv.2.2.1)))
            (fkRectHorizontalCutEdge_crossesVerticalSeam R a ha))
  rw [heq]
  exact hchain


theorem fkRectForceDualPullbackUnitPattern_verticalWinding_of_columnBand
    (R : FKRectTorus) (right : Nat) (hright : 1 <= right)
    (omega : R.Configuration)
    (t : Finset
      (FKRectColumnBandVertex R 1 right 1 (R.height - 1) ×
        FKRectColumnBandVertex R 1 right 1 (R.height - 1)))
    (hpair :
      (fkRectColumnBandRowOne R 1 right (fkRectUnitGapColumn R)
          (by rfl) hright,
        fkRectColumnBandLastRow R 1 right (fkRectUnitGapColumn R)
          (by rfl) hright) ∈ t)
    (haux : fkRectUnitDualBarrierAuxiliary R right t omega) :
    let forced := fkRectForceIndexedPattern R
      (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
      (fkRectDualPullbackConfiguration R
        (fkRectAllButOneOpenConfiguration R
          (fkRectUnitLeftBarrierGap R))) omega
    forced ∈ fkRectVerticalWindingEvent R ∧
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectColumnBandVertex R 1 right 1 (R.height - 1) -> R.Vertex)
          (fkRectFullGraphConfiguration R forced) ∈
        fkRectInducedConnectionChainEvent R
          (fkRectColumnBand R 1 right 1 (R.height - 1)) t := by
  dsimp only
  let eta := fkRectDualPullbackConfiguration R
    (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R))
  let forced := fkRectForceIndexedPattern R
    (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) eta omega
  have hchain :
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectColumnBandVertex R 1 right 1 (R.height - 1) -> R.Vertex)
          (fkRectFullGraphConfiguration R forced) ∈
        fkRectInducedConnectionChainEvent R
          (fkRectColumnBand R 1 right 1 (R.height - 1)) t := by
    exact fkRectForceDualPullbackSeam_preserves_columnBand_chain
      R 1 right 1 (R.height - 1) (by rfl) eta omega t haux.1
  have hreach := fkRectColumnBand_connection_reachable_verticalCut
    R 1 right 1 (R.height - 1) (by rfl) forced
      (fkRectColumnBandRowOne R 1 right (fkRectUnitGapColumn R)
        (by rfl) hright)
      (fkRectColumnBandLastRow R 1 right (fkRectUnitGapColumn R)
        (by rfl) hright)
      (hchain _ hpair)
  have hattach : forced (fkRectRowZeroAttachmentEdgeAt R
      (fkRectUnitGapColumn R)) = true := by
    dsimp [forced, eta]
    rw [fkRectForceDualPullbackUnitPattern_attachment_eq]
    exact haux.2
  have hwinding := fkRectVerticalWindingEvent_of_rightBand_reachable
    R (fkRectUnitGapColumn R) forced hreach
      (fkRectForceDualPullbackUnitPattern_verticalSeam_open R omega)
      hattach
  exact ⟨hwinding, hchain⟩


theorem fkRectForceDualPullbackUnitPattern_verticalWinding_of_columnBandSpans
    (R : FKRectTorus) (right : Nat) (hright : 1 <= right)
    (omega : R.Configuration)
    (t : Finset
      (FKRectColumnBandVertex R 1 right 1 (R.height - 1) ×
        FKRectColumnBandVertex R 1 right 1 (R.height - 1)))
    (hspans : FKRectColumnBandConnectionChainSpans R 1 right
      (fkRectUnitGapColumn R) (by rfl) hright t)
    (haux : fkRectUnitDualBarrierAuxiliary R right t omega) :
    let forced := fkRectForceIndexedPattern R
      (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
      (fkRectDualPullbackConfiguration R
        (fkRectAllButOneOpenConfiguration R
          (fkRectUnitLeftBarrierGap R))) omega
    forced ∈ fkRectVerticalWindingEvent R ∧
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectColumnBandVertex R 1 right 1 (R.height - 1) -> R.Vertex)
          (fkRectFullGraphConfiguration R forced) ∈
        fkRectInducedConnectionChainEvent R
          (fkRectColumnBand R 1 right 1 (R.height - 1)) t := by
  dsimp only
  let eta := fkRectDualPullbackConfiguration R
    (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R))
  let forced := fkRectForceIndexedPattern R
    (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) eta omega
  have hchain :
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectColumnBandVertex R 1 right 1 (R.height - 1) -> R.Vertex)
          (fkRectFullGraphConfiguration R forced) ∈
        fkRectInducedConnectionChainEvent R
          (fkRectColumnBand R 1 right 1 (R.height - 1)) t := by
    exact fkRectForceDualPullbackSeam_preserves_columnBand_chain
      R 1 right 1 (R.height - 1) (by rfl) eta omega t haux.1
  have hreachInduced := hspans _ hchain
  have hreach := fkRectColumnBand_connection_reachable_verticalCut
    R 1 right 1 (R.height - 1) (by rfl) forced
      (fkRectColumnBandRowOne R 1 right (fkRectUnitGapColumn R)
        (by rfl) hright)
      (fkRectColumnBandLastRow R 1 right (fkRectUnitGapColumn R)
        (by rfl) hright)
      hreachInduced
  have hattach : forced (fkRectRowZeroAttachmentEdgeAt R
      (fkRectUnitGapColumn R)) = true := by
    dsimp [forced, eta]
    rw [fkRectForceDualPullbackUnitPattern_attachment_eq]
    exact haux.2
  have hwinding := fkRectVerticalWindingEvent_of_rightBand_reachable
    R (fkRectUnitGapColumn R) forced hreach
      (fkRectForceDualPullbackUnitPattern_verticalSeam_open R omega)
      hattach
  exact ⟨hwinding, hchain⟩

end
end StatMech.FrontierD
