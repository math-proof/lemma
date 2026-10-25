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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceNoLoop.Part4


namespace StatMech.FrontierD

noncomputable section

open Filter Topology


set_option maxHeartbeats 800000 in


theorem fkRectZeroTurnSelectedPrimalOrRightBoundaryContact_side_injective
    (R : FKRectTorus) (omega : R.Configuration) :
    Function.Injective fun C : FKRectZeroTurnCutRemainderComponent R omega =>
      (fkRectZeroTurnSelectedPrimalOrRightBoundaryContact R omega C,
        fkRectZeroTurnRemainderSide R omega C) := by
  intro C D h
  have hchoice := congrArg Prod.fst h
  have hside := congrArg Prod.snd h
  change fkRectZeroTurnSelectedPrimalOrRightBoundaryContact R omega C =
    fkRectZeroTurnSelectedPrimalOrRightBoundaryContact R omega D at hchoice
  change fkRectZeroTurnRemainderSide R omega C =
    fkRectZeroTurnRemainderSide R omega D at hside
  by_cases hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C
  · by_cases hD : FKRectZeroTurnUsesPrimalTouchedCrossings R omega D
    · rw [fkRectZeroTurnSelectedPrimalOrRightBoundaryContact,
        dif_pos hC,
        fkRectZeroTurnSelectedPrimalOrRightBoundaryContact,
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
    · simp [fkRectZeroTurnSelectedPrimalOrRightBoundaryContact,
        hC, hD] at hchoice
  · by_cases hD : FKRectZeroTurnUsesPrimalTouchedCrossings R omega D
    · simp [fkRectZeroTurnSelectedPrimalOrRightBoundaryContact,
        hC, hD] at hchoice
    · rw [fkRectZeroTurnSelectedPrimalOrRightBoundaryContact,
        dif_neg hC,
        fkRectZeroTurnSelectedPrimalOrRightBoundaryContact,
        dif_neg hD] at hchoice
      injection hchoice with hcontact
      apply fkRectZeroTurnRemainder_eq_of_dualComponent_eq_of_sameSide
        R omega C D _ hside
      apply
        fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_sharedRightBoundaryContact
          R omega C D
            (fkRectZeroTurnSelectedDualRightBoundaryContact R omega C)
      · exact fkRectZeroTurnSelectedDualRightBoundaryContact_mem R omega C
      · rw [hcontact]
        exact fkRectZeroTurnSelectedDualRightBoundaryContact_mem R omega D


theorem
    fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_height_unconditional
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectZeroTurnCutRemainderCount R omega ≤
      2 * fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) + 2 * R.height := by
  let encode : FKRectZeroTurnCutRemainderComponent R omega →
      FKRectZeroTurnPrimalOrRightBoundaryContact R omega × Bool :=
    fun C =>
      (fkRectZeroTurnSelectedPrimalOrRightBoundaryContact R omega C,
        fkRectZeroTurnRemainderSide R omega C)
  have hcard := Fintype.card_le_of_injective encode
    (fkRectZeroTurnSelectedPrimalOrRightBoundaryContact_side_injective
      R omega)
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
  rw [hrem, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_sum, hprimal, Fintype.card_fin] at hcard
  omega


theorem fkRect_not_crossesVerticalSeam_indexedEdge_of_not_mem_horizontalCut
    (R : FKRectTorus) (a : R.EdgeIndex)
    (ha : a ∉ fkRectHorizontalCutEdges R) :
    ¬ fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a) := by
  rw [mem_fkRectHorizontalCutEdges_iff] at ha
  rcases a with ⟨b, x, y⟩
  change y.val ≠ 0 at ha
  have hh := R.height_gt_two
  have hylt := y.isLt
  intro hcross
  cases b
  · by_cases hy : Even y.val <;>
      simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
        hy, if_true, fkRectCrossesVerticalSeam_mk] at hcross
    all_goals rw [fkRectCyclicPred_val] at hcross
    all_goals split at hcross <;> omega
  · simp only [fkRectTorusIndexedEdge, if_true,
      fkRectCrossesVerticalSeam_mk] at hcross
    rw [fkRectCyclicPred_val] at hcross
    split at hcross <;> omega


theorem exists_fkRectHorizontalCutEdge_mem_remainderBoundaryCycleWalk
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hC : ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
    ∃ a : R.EdgeIndex, a ∈ fkRectHorizontalCutEdges R ∧
      fkRectTorusIndexedEdge R a ∈
        (fkRectBlackBoundaryPrimalCycleWalk R omega
          (fkRectZeroTurnRemainderBlackDart R omega C)).edges := by
  unfold FKRectZeroTurnUsesPrimalTouchedCrossings
    FKRectWalkAvoidsRowSeam at hC
  push Not at hC
  obtain ⟨e, he, hcross⟩ := hC
  have hex : ∃ x y : R.Vertex, e = s(x, y) := by
    induction e using Sym2.inductionOn with
    | _ x y => exact ⟨x, y, rfl⟩
  obtain ⟨x, y, rfl⟩ := hex
  have hadj := (fkRectBlackBoundaryPrimalCycleWalk R omega
    (fkRectZeroTurnRemainderBlackDart R omega C)).adj_of_mem_edges he
  rcases hadj with ⟨a, haopen, haedge⟩
  refine ⟨a, ?_, ?_⟩
  · by_contra hnot
    exact (fkRect_not_crossesVerticalSeam_indexedEdge_of_not_mem_horizontalCut
      R a hnot) (by rwa [haedge])
  · rwa [haedge]


end
end StatMech.FrontierD
