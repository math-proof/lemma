/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaLowRowMarkedOutputData_mem_targetFiber
    (G : SimpleGraph V) (sites : I -> V) {i j : I}
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (d : LPReplicaLowRowMarkedOutputData G sites q z) :
    d.output ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
      (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) := by
  classical
  simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiber,
    Finset.mem_filter]
  constructor
  · simp only [lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact d.balanced
  · unfold lpReplicaOffdiagDecoratedTargetCrossTrace
      lpReplicaOffdiagDecoratedSourceCrossTrace
    rw [d.state_eq]
    exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle G sites q _ _


theorem lpReplicaLowRowMarkedOutputData_rowMask_card_eq_two
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z)
    (d : LPReplicaLowRowMarkedOutputData G sites q z) :
    (lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q d.output).2).card = 2 := by
  classical
  let state := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z
  let M := lpReplicaOrbitFourColorSlotRowMask G sites q state
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2
  let slot := E d.copy
  have hMcard : M.card = 3 := by
    exact lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_card
      G sites hsite hij q hcard z hlow
  have hslotM : slot ∈ M := by
    change slot ∈ lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
    rw [lpReplicaOffdiagDecoratedSource_rank_five_lowRow_rowMask_eq_activeSlots
      G sites hsite hij q hcard z hlow]
    rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
    simpa only [slot, E, Equiv.symm_apply_apply] using d.copy_active
  have hslots : lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
      z.1.1.2 z.2.2 {d.copy} = {slot} := by
    simp [lpReplicaOrbitCommonSlotsOfCopies, slot, E]
  have hdiff : M ∆ {slot} = M \ {slot} := by
    ext x
    by_cases hx : x = slot
    · subst x
      simp [Finset.mem_symmDiff, hslotM]
    · simp [Finset.mem_symmDiff, hx]
  rw [d.state_eq, lpReplicaOrbitFourColorSlotRowMask_crossToggle,
    hslots]
  change (M ∆ {slot}).card = 2
  rw [hdiff, Finset.card_sdiff_of_subset (by simpa using hslotM),
    hMcard, Finset.card_singleton]

set_option maxHeartbeats 800000 in


theorem lpReplicaOffdiagDecoratedSourceSlotState_current_copy
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1) :
    (lpReplicaRowTagEquivFin4.symm
      ((lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z).color
        ⟨lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
          z.1.1.2 z.2.2 c, Finset.mem_univ _⟩)).2 =
      ((lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c).2 := by
  have htag :=
    lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
  change (lpReplicaRowTagEquivFin4.symm
      ((lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1.1
        z.1.1.2 z.2.2 _).color
        ⟨lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
          z.1.1.2 z.2.2 c, Finset.mem_univ _⟩)).2 = _
  rw [lpReplicaOrbitFourColorSlotStateOfTag_color_copy, htag]
  simp


end
end StatMech.Ising
