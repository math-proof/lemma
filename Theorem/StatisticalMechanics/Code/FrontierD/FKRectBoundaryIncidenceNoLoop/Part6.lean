/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceConnected.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveMixedNoLoopHeight
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceNoLoop.Part6


namespace StatMech.FrontierD

noncomputable section

open Filter Topology


set_option maxHeartbeats 800000 in

theorem fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge_side_injective
    (R : FKRectTorus) (omega : R.Configuration) :
    Function.Injective fun C : FKRectZeroTurnCutRemainderComponent R omega =>
      (fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge R omega C,
        fkRectZeroTurnRemainderSide R omega C) := by
  intro C D h
  have hchoice := congrArg Prod.fst h
  have hside := congrArg Prod.snd h
  change fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge R omega C =
    fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge R omega D at hchoice
  change fkRectZeroTurnRemainderSide R omega C =
    fkRectZeroTurnRemainderSide R omega D at hside
  by_cases hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C
  · by_cases hD : FKRectZeroTurnUsesPrimalTouchedCrossings R omega D
    · rw [fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge,
        dif_pos hC, fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge,
        dif_pos hD] at hchoice
      injection hchoice with hcross
      apply fkRectZeroTurnRemainder_eq_of_primalComponent_eq_of_sameSide
        R omega C D _ hside
      apply fkRectZeroTurnRemainderPrimalComponent_eq_of_shared_touchedCrossing
        R omega C D
          (fkRectZeroTurnSelectedPrimalTouchedCrossing R omega C hC)
      · exact fkRectZeroTurnSelectedPrimalTouchedCrossing_mem
          R omega C hC
      · rw [hcross]
        exact fkRectZeroTurnSelectedPrimalTouchedCrossing_mem
          R omega D hD
    · simp [fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge,
        hC, hD] at hchoice
  · by_cases hD : FKRectZeroTurnUsesPrimalTouchedCrossings R omega D
    · simp [fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge,
        hC, hD] at hchoice
    · rw [fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge,
        dif_neg hC, fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge,
        dif_neg hD] at hchoice
      injection hchoice with hedge
      apply fkRectZeroTurnRemainder_eq_of_primalComponent_eq_of_sameSide
        R omega C D _ hside
      apply fkRectZeroTurnRemainderPrimalComponent_eq_of_shared_boundaryEdge
        R omega C D
          (fkRectZeroTurnSelectedHorizontalCutEdge R omega C hC).1
      · exact fkRectZeroTurnSelectedHorizontalCutEdge_mem_boundaryCycleWalk
          R omega C hC
      · rw [hedge]
        exact fkRectZeroTurnSelectedHorizontalCutEdge_mem_boundaryCycleWalk
          R omega D hD


theorem
    fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_four_width_unconditional
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) + 4 * R.width := by
  let encode : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectZeroTurnPrimalOrHorizontalCutEdge R omega × Bool :=
    fun C =>
      (fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge R omega C,
        fkRectZeroTurnRemainderSide R omega C)
  have hcard := Fintype.card_le_of_injective encode
    (fkRectZeroTurnSelectedPrimalOrHorizontalCutEdge_side_injective R omega)
  have hrem : Fintype.card (FKRectZeroTurnCutRemainderComponent R omega) =
      fkRectZeroTurnCutRemainderCount R omega := by
    classical
    unfold FKRectZeroTurnCutRemainderComponent
      fkRectZeroTurnCutRemainderCount
    exact Fintype.card_ofFinset
      (fkRectZeroTurnCutRemainderComponents R omega) (by simp)
  have hprimal :
      Fintype.card (FKRectRawPrimalHorizontalCrossingComponent R omega) =
        fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) := by
    unfold fkRectRawHorizontalCrossingClusterCount
    exact Fintype.card_congr (Equiv.refl _)
  have hcut : Fintype.card (FKRectHorizontalCutEdge R) = 2 * R.width := by
    rw [← fkRectHorizontalCutEdges_card R]
    exact Fintype.card_ofFinset (fkRectHorizontalCutEdges R) (by simp)
  rw [hrem, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_sum, hprimal, hcut] at hcard
  omega


theorem fkRectCritical_zeroTurnAbove_le_half_of_boundaryIncidenceAdaptiveTail
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) (n : Nat)
    (hsmall : Nat.choose R.height (n + 1) *
        ((FK.freeInfiniteVolume 2
          (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
          (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
          (zero_lt_one.trans_le hq) :
            MeasureTheory.Measure (ConfigSpace
              (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) ≤
      FK.cFE (fkRectCriticalP q) q ^
        (2 * R.width + R.height) / 2) :
    fkRectCriticalZeroTurnAboveMass R q
        (2 * R.width + (4 * R.width + 2 * n)) ≤ (1 : Real) / 2 := by
  let K : R.Configuration → Nat := fun eta =>
    2 * fkRectRawHorizontalCrossingClusterCount R
      (fkRectForceCutClosed R eta) + 4 * R.width
  have htop : ∀ omega : R.Configuration,
      fkRectZeroTurnLoopCount R omega ≤
        2 * R.width + K (fkRectForceCutClosed R omega) := by
    intro omega
    apply (fkRectZeroTurnLoopCount_le_two_width_add_cutRemainder
      R omega).trans
    apply Nat.add_le_add_left
    dsimp [K]
    simpa using
      (fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_four_width_unconditional
        R omega)
  have htransfer := fkRectCritical_zeroTurnAbove_cut_transfer
    R hq K htop (4 * R.width + 2 * n)
  let A : Set R.Configuration :=
    {eta | n < fkRectRawHorizontalCrossingClusterCount R
      (fkRectForceCutClosed R eta)}
  have hset :
      {eta | FKRectCutClosedConfiguration R eta ∧
          4 * R.width + 2 * n < K eta} =
        {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A} := by
    ext eta
    simp only [Set.mem_setOf_eq, A, K]
    constructor <;> intro h
    · exact ⟨h.1, by omega⟩
    · exact ⟨h.1, by omega⟩
  rw [hset] at htransfer
  have htop' : FK.cFE (fkRectCriticalP q) q ^
        (2 * R.width + R.height) *
      fkRectCriticalZeroTurnAboveMass R q
        (2 * R.width + (4 * R.width + 2 * n)) ≤
    fkRectCriticalEventMass R q
      {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A} := by
    exact htransfer
  rw [← closedMass_mul_fkRectCriticalCutFreeEventMass R hq A] at htop'
  have hcutNonneg : 0 ≤ fkRectCriticalCutFreeEventMass R q A :=
    fkRectCriticalCutFreeEventMass_nonneg R hq A
  have hmassLe :
      fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) *
          fkRectCriticalCutFreeEventMass R q A ≤
        fkRectCriticalCutFreeEventMass R q A := by
    nlinarith [fkRectCriticalClosedMass_cut_le_one R hq]
  have hbinom : fkRectCriticalCutFreeEventMass R q A ≤
      Nat.choose R.height (n + 1) *
        ((FK.freeInfiniteVolume 2
          (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
          (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
          (zero_lt_one.trans_le hq) :
            MeasureTheory.Measure (ConfigSpace
              (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) := by
    exact fkRectCriticalCutFree_primalCrossingTail_le_choose_mul_pow
      R hq n
  have hc : 0 < FK.cFE (fkRectCriticalP q) q :=
    FK.cFE_pos
      (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
      (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq
  have hpow : 0 < FK.cFE (fkRectCriticalP q) q ^
      (2 * R.width + R.height) := pow_pos hc _
  have hfinal := htop'.trans (hmassLe.trans (hbinom.trans hsmall))
  nlinarith


theorem
    tendsto_allSectorNormalization_negLog_div_height_zero_of_boundaryIncidenceAdaptiveTail
    (R : Nat → FKRectTorus) {q : Real} (hq : 4 < q) (n : Nat → Nat)
    (hsmall : ∀ k,
      Nat.choose (R k).height (n k + 1) *
          ((FK.freeInfiniteVolume 2
            (fkRectCriticalP_pos (by linarith : 0 < q))
            (fkRectCriticalP_lt_one (by linarith : 0 < q))
            (by linarith : 0 < q) :
              MeasureTheory.Measure (ConfigSpace
                (Sym2 (StatMech.Lattice.Site 2)))).real
            (FK.boxBdryConnEvent 2 ((R k).width - 2))) ^ (n k + 1) ≤
        FK.cFE (fkRectCriticalP q) q ^
          (2 * (R k).width + (R k).height) / 2)
    (hwidth : Tendsto (fun k ↦ ((R k).width : Real) / (R k).height)
      atTop (nhds 0))
    (hn : Tendsto (fun k ↦ (n k : Real) / (R k).height)
      atTop (nhds 0))
    (hheight : Tendsto (fun k ↦ (R k).height) atTop atTop) :
    Tendsto (fun k ↦
      -Real.log (fkRectAllSectorNormalization (R k) q) /
        (R k).height) atTop (nhds 0) := by
  let L : Nat → Nat := fun k =>
    2 * (R k).width + (4 * (R k).width + 2 * n k)
  apply tendsto_allSectorNormalization_negLog_div_height_zero_of_sublinear_tail
    R hq L
  · intro k
    exact
      fkRectCritical_zeroTurnAbove_le_half_of_boundaryIncidenceAdaptiveTail
        (R k) (by linarith) (n k) (hsmall k)
  · have hcomb := (hwidth.const_mul (6 : Real)).add
        (hn.const_mul (2 : Real))
    have hcomb0 : Tendsto (fun k =>
        6 * ((R k).width : Real) / (R k).height +
          2 * (n k : Real) / (R k).height) atTop (nhds 0) := by
      simpa [mul_div_assoc] using hcomb
    apply hcomb0.congr'
    filter_upwards [] with k
    dsimp [L]
    push_cast
    ring
  · exact hheight


end
end StatMech.FrontierD
