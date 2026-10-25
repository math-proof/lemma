/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagDecoratedSource_rank_five_highRow_singletonToggle_mask_four
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh : LPReplicaOffdiagDecoratedSource.IsHighRowRankFive
      G sites i j q z)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hstate : (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q y).2 =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
          z.1.1.2 z.2.2 {c})
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
    (lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q y).2).card = 4 := by
  classical
  let slot := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2 c
  have hsourceMask :=
    lpReplicaOffdiagDecoratedSource_rank_five_highRow_rowMask_eq_univ
      G sites hsite hij q hcard z hhigh
  rw [hstate, lpReplicaOrbitFourColorSlotRowMask_crossToggle, hsourceMask]
  have hslots : lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
      z.1.1.2 z.2.2 {c} = {slot} := by
    unfold lpReplicaOrbitCommonSlotsOfCopies
    rw [Finset.map_singleton]
    rfl
  have hdiff : (Finset.univ ∆ ({slot} : Finset
      (LPReplicaOrbitCommonSlot G sites q))) = Finset.univ \ {slot} := by
    ext x
    simp [Finset.mem_symmDiff]
  rw [hslots, hdiff, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, hcard, Finset.card_singleton]


theorem lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskFour_rank_five_nonempty_of_resolvableHighRow
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hresolve : LPReplicaOffdiagDecoratedSource.IsResolvableHighRowRankFive
      G sites i j q z) :
    (lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
      G sites i j q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) 4).Nonempty := by
  classical
  rcases hresolve.1 with hsat | hthree
  · rcases hresolve.2 hsat with ⟨c, hc⟩ | ⟨c, hc⟩
    · obtain ⟨y, hyBal, hyTrace, hyMask⟩ :=
        lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_mask_four_of_iSeam
          G sites hsite hij q hcard z hsat c hc
      refine ⟨y, ?_⟩
      simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive,
        lpReplicaOffdiagBalancedOutputCrossTraceFiber,
        lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨⟨hyBal, hyTrace⟩, hyMask⟩
    · obtain ⟨y, hyBal, hstate⟩ :=
        lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_of_jSeam
          G sites q z hsat c hc
      let Y : LPReplicaOffdiagDecoratedTarget G sites i j q := Sum.inr y
      have hyMask :=
        lpReplicaOffdiagDecoratedSource_rank_five_highRow_singletonToggle_mask_four
          G sites hsite hij q hcard z (Or.inl hsat) Y c hstate
      refine ⟨Y, ?_⟩
      simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive,
        lpReplicaOffdiagBalancedOutputCrossTraceFiber,
        lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨⟨hyBal, ?_⟩, hyMask⟩
      unfold lpReplicaOffdiagDecoratedTargetCrossTrace
        lpReplicaOffdiagDecoratedSourceCrossTrace
      rw [hstate]
      exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
        G sites q _ _
  · obtain ⟨y, c, hyBal, _, hstate⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_exists_target_of_active_card_eq_three
        G sites hsite hij q hcard z hthree.1
    have hyMask :=
      lpReplicaOffdiagDecoratedSource_rank_five_highRow_singletonToggle_mask_four
        G sites hsite hij q hcard z (Or.inr hthree) y c hstate
    refine ⟨y, ?_⟩
    simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive,
      lpReplicaOffdiagBalancedOutputCrossTraceFiber,
      lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨⟨hyBal, ?_⟩, hyMask⟩
    unfold lpReplicaOffdiagDecoratedTargetCrossTrace
      lpReplicaOffdiagDecoratedSourceCrossTrace
    rw [hstate]
    exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
      G sites q _ _


theorem lpReplicaLowRowMarkedOutputData_mem_targetFiberRowMaskTwo
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z)
    (d : LPReplicaLowRowMarkedOutputData G sites q z) :
    d.output ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
      G sites i j q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) 2 := by
  classical
  simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive,
    Finset.mem_filter]
  exact ⟨lpReplicaLowRowMarkedOutputData_mem_targetFiber
      G sites q z d,
    lpReplicaLowRowMarkedOutputData_rowMask_card_eq_two
      G sites hsite hij q hcard z hlow d⟩


theorem lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskTwo_disjoint_four
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    ¬ (y ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
          G sites i j q u 2 ∧
        y ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
          G sites i j q u 4) := by
  classical
  intro hy
  have htwo := (Finset.mem_filter.mp hy.1).2
  have hfour := (Finset.mem_filter.mp hy.2).2
  omega


theorem lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_maskFourTarget
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
      G sites i j q u).card <=
      (lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
        G sites i j q u 4).card := by
  classical
  have hsource :=
    lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_one
      G sites hsite hij q hcard u
  by_cases hempty :
      (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
        G sites i j q u).Nonempty
  · obtain ⟨z, hz⟩ := hempty
    have hz' := Finset.mem_filter.mp hz
    have htarget :=
      lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskFour_rank_five_nonempty_of_resolvableHighRow
        G sites hsite hij q hcard z hz'.2
    have htrace := (Finset.mem_filter.mp hz'.1).2
    rw [htrace] at htarget
    exact Nat.le_trans hsource (Finset.card_pos.mpr htarget)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.card_empty]
    exact Nat.zero_le _


end
end StatMech.Ising
