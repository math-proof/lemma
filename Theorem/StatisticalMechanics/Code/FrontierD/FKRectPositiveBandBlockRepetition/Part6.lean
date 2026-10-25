/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierLocalizedCycle
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierForceTopology
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierPattern
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierRate
import Theorem.StatisticalMechanics.Code.FK.TwoPointPathLower
import Def.StatisticalMechanics.Code.FrontierD.FKRectPositiveBandBlockRepetition.Part6
open Set SimpleGraph Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem fkRectPositiveBandBlockAssembledEvent_isIncreasing
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    IsIncreasing (fkRectPositiveBandBlockAssembledEvent B hheight) := by
  intro omega tau hot hmem
  exact ⟨⟨⟨
    fkRectEvenRowBlockIntersection_isIncreasing
      R B.carrier B.start B.finish B.step
        (fkRectPositiveBandBulkBlocks B) hot hmem.1.1.1,
    fkRectPositiveBandBlockBottomConnectorEvent_isIncreasing
      B hheight hot hmem.1.1.2⟩,
    fkRectPositiveBandBlockTopConnectorEvent_isIncreasing
      B hheight hot hmem.1.2⟩,
    fkRectUnitAttachmentOpenEvent_isIncreasing R hot hmem.2⟩


theorem fkRectPositiveBandBlock_auxiliary_of_bulk_connectors
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (omega : R.Configuration)
    (hbulk : omega ∈ fkRectEvenRowBlockIntersection
      R B.carrier B.start B.finish B.step
        (fkRectPositiveBandBulkBlocks B))
    (hbottom : omega ∈
      fkRectPositiveBandBlockBottomConnectorEvent B hheight)
    (htop : omega ∈
      fkRectPositiveBandBlockTopConnectorEvent B hheight)
    (hattach : omega ∈ fkRectUnitAttachmentOpenEvent R) :
    omega ∈ fkRectUnitDualBarrierAuxiliary R (4 * scale + 1)
      (fkRectPositiveBandBlockAuxiliaryPairs B hheight) := by
  constructor
  · intro pair hpair
    rcases Finset.mem_union.mp hpair with hpair | hpair
    · exact fkRectPositiveBandBlockIntersection_inducedChain
        B hheight omega hbulk pair hpair
    · simp only [fkRectPositiveBandBlockConnectorPairs,
        Finset.mem_insert, Finset.mem_singleton] at hpair
      rcases hpair with rfl | rfl
      · change (FK.openSub
          (fkRectInducedGraph R
            (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)))
          (FK.ocd_innerRestrict Subtype.val
            (fkRectFullGraphConfiguration R omega))).Reachable _ _
        rw [fkRectInduced_openSub_fullGraphConfiguration_eq]
        exact hbottom
      · change (FK.openSub
          (fkRectInducedGraph R
            (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)))
          (FK.ocd_innerRestrict Subtype.val
            (fkRectFullGraphConfiguration R omega))).Reachable _ _
        rw [fkRectInduced_openSub_fullGraphConfiguration_eq]
        exact htop
  · exact hattach

theorem fkRectPositiveBandBlockAssembledEvent_subset_auxiliary
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    fkRectPositiveBandBlockAssembledEvent B hheight ⊆
      fkRectUnitDualBarrierAuxiliary R (4 * scale + 1)
        (fkRectPositiveBandBlockAuxiliaryPairs B hheight) := by
  intro omega hmem
  exact fkRectPositiveBandBlock_auxiliary_of_bulk_connectors
    B hheight omega hmem.1.1.1 hmem.1.1.2 hmem.1.2 hmem.2


theorem exists_fkRectPositiveBandBlock_localizedVerticalCycle
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (hproper : 4 * scale + 2 < R.width)
    (omega : R.Configuration)
    (hbulk : omega ∈ fkRectEvenRowBlockIntersection
      R B.carrier B.start B.finish B.step
        (fkRectPositiveBandBulkBlocks B))
    (hbottom : omega ∈
      fkRectPositiveBandBlockBottomConnectorEvent B hheight)
    (htop : omega ∈
      fkRectPositiveBandBlockTopConnectorEvent B hheight)
    (hattach : omega ∈ fkRectUnitAttachmentOpenEvent R) :
    let forced := fkRectForceIndexedPattern R
      (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
      (fkRectDualPullbackConfiguration R
        (fkRectAllButOneOpenConfiguration R
          (fkRectUnitLeftBarrierGap R))) omega
    ∃ z : (fkRectOpenGraph R forced).Walk
        (fkRectRowOneVertex R (fkRectUnitGapColumn R))
        (fkRectRowOneVertex R (fkRectUnitGapColumn R)),
      fkRectWalkWinding R z = (0, 1) ∧
      ∀ v ∈ z.support,
        1 ≤ v.1.val ∧ v.1.val ≤ 4 * scale + 1 := by
  exact exists_fkRectForceDualPullbackUnitPattern_localizedVerticalCycle
    R (4 * scale + 1) (by omega) hproper omega
      (fkRectPositiveBandBlockAuxiliaryPairs B hheight)
      (fkRectPositiveBandBlockAuxiliaryPairs_spans B hheight)
      (fkRectPositiveBandBlock_auxiliary_of_bulk_connectors
        B hheight omega hbulk hbottom htop hattach)


theorem fkRectCritical_positiveBandBulkLower
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hq : 1 ≤ q) :
    B.massFloor ^
        fkRectPositiveBandBulkBlocks B ≤
      fkRectCriticalEventMass R q
        (fkRectEvenRowBlockIntersection R B.carrier B.start B.finish
          B.step (fkRectPositiveBandBulkBlocks B)) := by
  apply fkRectCritical_evenRowBlockLower_pow_le_intersection
    R B.carrier B.start B.finish B.step
      (fkRectPositiveBandBulkBlocks B) B.step_even hq
  · exact B.massFloor_nonneg
  · exact B.mass_lower


theorem fkRectCritical_positiveBandAuxiliaryLower
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (hq : 1 ≤ q)
    {bottom top attachment : Real}
    (hbottom0 : 0 ≤ bottom) (htop0 : 0 ≤ top)
    (hattachment0 : 0 ≤ attachment)
    (hbottom : bottom ≤ fkRectCriticalEventMass R q
      (fkRectPositiveBandBlockBottomConnectorEvent B hheight))
    (htop : top ≤ fkRectCriticalEventMass R q
      (fkRectPositiveBandBlockTopConnectorEvent B hheight))
    (hattachment : attachment ≤ fkRectCriticalEventMass R q
      (fkRectUnitAttachmentOpenEvent R)) :
    ((B.massFloor ^
          fkRectPositiveBandBulkBlocks B * bottom) * top) * attachment ≤
      fkRectCriticalEventMass R q
        (fkRectUnitDualBarrierAuxiliary R (4 * scale + 1)
          (fkRectPositiveBandBlockAuxiliaryPairs B hheight)) := by
  let A := fkRectEvenRowBlockIntersection
    R B.carrier B.start B.finish B.step
      (fkRectPositiveBandBulkBlocks B)
  let C := fkRectPositiveBandBlockBottomConnectorEvent B hheight
  let D := fkRectPositiveBandBlockTopConnectorEvent B hheight
  let E := fkRectUnitAttachmentOpenEvent R
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hAinc : IsIncreasing A :=
    fkRectEvenRowBlockIntersection_isIncreasing
      R B.carrier B.start B.finish B.step
        (fkRectPositiveBandBulkBlocks B)
  have hCinc : IsIncreasing C :=
    fkRectPositiveBandBlockBottomConnectorEvent_isIncreasing B hheight
  have hDinc : IsIncreasing D :=
    fkRectPositiveBandBlockTopConnectorEvent_isIncreasing B hheight
  have hEinc : IsIncreasing E := fkRectUnitAttachmentOpenEvent_isIncreasing R
  have hACinc : IsIncreasing (A ∩ C) := by
    intro omega tau hot hmem
    exact ⟨hAinc hot hmem.1, hCinc hot hmem.2⟩
  have hACDinc : IsIncreasing ((A ∩ C) ∩ D) := by
    intro omega tau hot hmem
    exact ⟨hACinc hot hmem.1, hDinc hot hmem.2⟩
  have hmA0 := fkRectCriticalEventMass_nonneg R hq0 A
  have hmC0 := fkRectCriticalEventMass_nonneg R hq0 C
  have hmD0 := fkRectCriticalEventMass_nonneg R hq0 D
  have hmE0 := fkRectCriticalEventMass_nonneg R hq0 E
  have hsource0 : 0 ≤ B.massFloor ^
      fkRectPositiveBandBulkBlocks B :=
    pow_nonneg B.massFloor_nonneg _
  have hbulk : B.massFloor ^
        fkRectPositiveBandBulkBlocks B ≤
      fkRectCriticalEventMass R q A := by
    exact fkRectCritical_positiveBandBulkLower B hq
  have hlower :
      ((B.massFloor ^
            fkRectPositiveBandBulkBlocks B * bottom) * top) * attachment ≤
        ((fkRectCriticalEventMass R q A *
            fkRectCriticalEventMass R q C) *
          fkRectCriticalEventMass R q D) *
            fkRectCriticalEventMass R q E := by
    calc
      ((B.massFloor ^
            fkRectPositiveBandBulkBlocks B * bottom) * top) * attachment ≤
          ((fkRectCriticalEventMass R q A * bottom) * top) * attachment := by
            apply mul_le_mul_of_nonneg_right _ hattachment0
            apply mul_le_mul_of_nonneg_right _ htop0
            exact mul_le_mul_of_nonneg_right hbulk hbottom0
      _ ≤ ((fkRectCriticalEventMass R q A *
            fkRectCriticalEventMass R q C) * top) * attachment := by
            apply mul_le_mul_of_nonneg_right _ hattachment0
            apply mul_le_mul_of_nonneg_right _ htop0
            exact mul_le_mul_of_nonneg_left hbottom hmA0
      _ ≤ ((fkRectCriticalEventMass R q A *
            fkRectCriticalEventMass R q C) *
          fkRectCriticalEventMass R q D) * attachment := by
            apply mul_le_mul_of_nonneg_right _ hattachment0
            exact mul_le_mul_of_nonneg_left htop
              (mul_nonneg hmA0 hmC0)
      _ ≤ ((fkRectCriticalEventMass R q A *
            fkRectCriticalEventMass R q C) *
          fkRectCriticalEventMass R q D) *
            fkRectCriticalEventMass R q E :=
            mul_le_mul_of_nonneg_left hattachment
              (mul_nonneg (mul_nonneg hmA0 hmC0) hmD0)
  have hproduct :
      ((fkRectCriticalEventMass R q A *
            fkRectCriticalEventMass R q C) *
          fkRectCriticalEventMass R q D) *
            fkRectCriticalEventMass R q E ≤
        fkRectCriticalEventMass R q (((A ∩ C) ∩ D) ∩ E) := by
    calc
      ((fkRectCriticalEventMass R q A *
            fkRectCriticalEventMass R q C) *
          fkRectCriticalEventMass R q D) *
            fkRectCriticalEventMass R q E ≤
          (fkRectCriticalEventMass R q (A ∩ C) *
            fkRectCriticalEventMass R q D) *
              fkRectCriticalEventMass R q E := by
            apply mul_le_mul_of_nonneg_right _ hmE0
            apply mul_le_mul_of_nonneg_right _ hmD0
            exact fkRectCriticalEventMass_mul_le_inter R hq hAinc hCinc
      _ ≤ fkRectCriticalEventMass R q ((A ∩ C) ∩ D) *
            fkRectCriticalEventMass R q E := by
            exact mul_le_mul_of_nonneg_right
              (fkRectCriticalEventMass_mul_le_inter
                R hq hACinc hDinc) hmE0
      _ ≤ fkRectCriticalEventMass R q (((A ∩ C) ∩ D) ∩ E) :=
            fkRectCriticalEventMass_mul_le_inter R hq hACDinc hEinc
  calc
    ((B.massFloor ^
          fkRectPositiveBandBulkBlocks B * bottom) * top) * attachment ≤
      fkRectCriticalEventMass R q (((A ∩ C) ∩ D) ∩ E) :=
        hlower.trans hproduct
    _ = fkRectCriticalEventMass R q
        (fkRectPositiveBandBlockAssembledEvent B hheight) := by rfl
    _ ≤ fkRectCriticalEventMass R q
        (fkRectUnitDualBarrierAuxiliary R (4 * scale + 1)
          (fkRectPositiveBandBlockAuxiliaryPairs B hheight)) :=
      fkRectCriticalEventMass_mono R hq0
        (fkRectPositiveBandBlockAssembledEvent_subset_auxiliary B hheight)


theorem fkRectCritical_concretePositiveBandAuxiliaryLower
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (hscale : 3 ≤ scale)
    (htall : 40 * scale + 6 < R.height - 1)
    (hproper : 4 * scale + 1 < R.width)
    (hq : 1 ≤ q) :
    ((B.massFloor ^
          fkRectPositiveBandBulkBlocks B *
        FK.cFE (fkRectCriticalP q) q ^
          ((4 * scale + 1) * (24 * scale + 4))) *
      FK.cFE (fkRectCriticalP q) q ^
        ((4 * scale + 1) * (40 * scale + 7))) *
      FK.cFE (fkRectCriticalP q) q ≤
    fkRectCriticalEventMass R q
      (fkRectUnitDualBarrierAuxiliary R (4 * scale + 1)
        (fkRectPositiveBandBlockAuxiliaryPairs B hheight)) := by
  have hc : 0 ≤ FK.cFE (fkRectCriticalP q) q :=
    (FK.cFE_pos (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
      (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq)) hq).le
  exact fkRectCritical_positiveBandAuxiliaryLower B hheight hq
    (pow_nonneg hc _) (pow_nonneg hc _) hc
    (fkRectCritical_cFE_pow_le_bottomConnector
      B hheight hproper hq)
    (fkRectCritical_cFE_pow_le_topConnector
      B hheight hscale htall hproper hq)
    (fkRectCritical_cFE_le_unitAttachmentOpenEvent R hq)


theorem fkRectCritical_concretePositiveBandDualBarrierLower
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (hscale : 3 ≤ scale)
    (htall : 40 * scale + 6 < R.height - 1)
    (hproper : 4 * scale + 2 < R.width)
    (hq : 1 ≤ q) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) *
      (((B.massFloor ^
            fkRectPositiveBandBulkBlocks B *
          FK.cFE (fkRectCriticalP q) q ^
            ((4 * scale + 1) * (24 * scale + 4))) *
        FK.cFE (fkRectCriticalP q) q ^
          ((4 * scale + 1) * (40 * scale + 7))) *
        FK.cFE (fkRectCriticalP q) q) ≤
      fkRectCriticalEventMass R q
        (fkRectDualPullbackSourceLeftBarrier R (4 * scale + 1)
          (fkRectUnitLeftBarrierGap R)) := by
  let A := fkRectUnitDualBarrierAuxiliary R (4 * scale + 1)
    (fkRectPositiveBandBlockAuxiliaryPairs B hheight)
  have haux :
      ((B.massFloor ^
            fkRectPositiveBandBulkBlocks B *
          FK.cFE (fkRectCriticalP q) q ^
            ((4 * scale + 1) * (24 * scale + 4))) *
        FK.cFE (fkRectCriticalP q) q ^
          ((4 * scale + 1) * (40 * scale + 7))) *
        FK.cFE (fkRectCriticalP q) q ≤
      fkRectCriticalEventMass R q A :=
    fkRectCritical_concretePositiveBandAuxiliaryLower
      B hheight hscale htall (by omega) hq
  have hforce : ∀ omega ∈ A,
      fkRectForceIndexedPattern R
          (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
          (fkRectDualPullbackConfiguration R
            (fkRectAllButOneOpenConfiguration R
              (fkRectUnitLeftBarrierGap R))) omega ∈
        fkRectDualPreimageEvent R
          (fkRectNoLeftStripCrossingEvent R (4 * scale + 1)) := by
    intro omega homega
    exact fkRectForceDualPullbackUnitPattern_mem_dualPreimage_noLeftStripCrossing
      R (4 * scale + 1) (by omega) (by omega) omega
        (fkRectPositiveBandBlockAuxiliaryPairs B hheight)
        (fkRectPositiveBandBlockAuxiliaryPairs_spans B hheight) homega
  have hpattern :=
    fkRectCritical_cFE_pow_width_mul_auxiliary_le_dualPullbackSource
      R (4 * scale + 1) hq (fkRectUnitLeftBarrierGap R) A hforce
  have hc : 0 ≤ FK.cFE (fkRectCriticalP q) q :=
    (FK.cFE_pos (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
      (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq)) hq).le
  exact (mul_le_mul_of_nonneg_left haux
    (pow_nonneg hc _)).trans hpattern


theorem fkRectWindingBlock_sourceBarrier_eventualUpper_of_eventuallyDualPullback_mul_pow
    (k scale leftRight : Nat) (hone : 1 ≤ leftRight)
    (hleft : leftRight + 1 < 2 * (k + 3))
    {q C a : Real} (hq : 1 ≤ q) (hC : 0 < C) (ha : 0 < a)
    (haux : ∀ᶠ blocks in atTop,
      C * a ^ (blocks + 1) ≤
        fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q
          (fkRectDualPullbackSourceLeftBarrier
            (fkRectWindingBlockVerticalFamily k scale blocks) leftRight
            (fkRectUnitLeftBarrierGap
              (fkRectWindingBlockVerticalFamily k scale blocks)))) :
    ∀ epsilon : Real, 0 < epsilon → ∀ᶠ blocks in atTop,
      -Real.log
          (fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectSourceLeftBarrier
              (fkRectWindingBlockVerticalFamily k scale blocks) leftRight
              (fkRectUnitLeftBarrierGap
                (fkRectWindingBlockVerticalFamily k scale blocks)))) /
          (fkRectWindingBlockVerticalFamily k scale blocks).height ≤
        -Real.log a / (2 * (scale + 1) : Real) + epsilon := by
  intro epsilon hepsilon
  let blockCost : Nat → Real := fun blocks ↦
    ((blocks + 1 : Nat) : Real) * (-Real.log a) /
      (fkRectWindingBlockVerticalFamily k scale blocks).height
  let dualConstant : Real := -Real.log ((1 / q) * C)
  let dualCost : Nat → Real := fun blocks ↦
    dualConstant /
      (fkRectWindingBlockVerticalFamily k scale blocks).height
  have hblock : Tendsto blockCost atTop
      (nhds (-Real.log a / (2 * (scale + 1) : Real))) := by
    have h := (fkRectWindingBlock_count_div_height_tendsto k scale).mul_const
      (-Real.log a)
    convert h using 1
    · funext blocks
      simp only [blockCost, fkRectWindingBlockVerticalFamily_height,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    · ring
  have hheightNat := tendsto_fkRectWindingBlockVerticalFamily_height k scale
  have hheight : Tendsto (fun blocks ↦
      ((fkRectWindingBlockVerticalFamily k scale blocks).height : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hheightNat
  have hdual : Tendsto dualCost atTop (nhds 0) :=
    hheight.const_div_atTop dualConstant
  have hevent : ∀ᶠ blocks in atTop,
      blockCost blocks + dualCost blocks <
        -Real.log a / (2 * (scale + 1) : Real) + epsilon :=
    (tendsto_order.1 (hblock.add hdual)).2 _ (by linarith)
  filter_upwards [hevent, haux] with blocks hcost hbound
  have hfinite := fkRectSourceBarrier_negLogRate_le_of_dualPullback_mul_pow
    (fkRectWindingBlockVerticalFamily k scale blocks) leftRight (blocks + 1)
    hone hleft hq hC ha hbound
  change -Real.log
          (fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectSourceLeftBarrier
              (fkRectWindingBlockVerticalFamily k scale blocks) leftRight
              (fkRectUnitLeftBarrierGap
                (fkRectWindingBlockVerticalFamily k scale blocks)))) /
        (fkRectWindingBlockVerticalFamily k scale blocks).height ≤
      -Real.log a / (2 * (scale + 1) : Real) + epsilon
  dsimp [blockCost, dualCost, dualConstant] at hcost
  exact hfinite.trans hcost.le

end
end StatMech.FrontierD
