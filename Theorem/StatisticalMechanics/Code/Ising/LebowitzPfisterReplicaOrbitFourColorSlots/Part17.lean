/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part17
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOrbitFourColorSlotRowMask_crossToggle
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOrbitFourColorSlotCrossToggle G sites q P s) =
      lpReplicaOrbitFourColorSlotRowMask G sites q s ∆ P := by
  classical
  ext x
  by_cases hp : x ∈ P
  · simp only [lpReplicaOrbitFourColorSlotRowMask, Finset.mem_filter,
      Finset.mem_univ, true_and, lpReplicaOrbitFourColorSlotCrossToggle,
      lpReplicaOrbitFourColorSlotRowToggle,
      lpReplicaOrbitFourColorSlotReflect, hp, if_pos,
      lpReplicaRowTagEquivFin4_symm_rowToggleFin4_fst,
      Finset.mem_symmDiff, not_true_eq_false, and_false, true_and]
    cases (lpReplicaRowTagEquivFin4.symm
      (s.color ⟨x, Finset.mem_univ _⟩)).1 <;> simp
  · simp only [lpReplicaOrbitFourColorSlotRowMask, Finset.mem_filter,
      Finset.mem_univ, true_and, lpReplicaOrbitFourColorSlotCrossToggle,
      lpReplicaOrbitFourColorSlotRowToggle,
      lpReplicaOrbitFourColorSlotReflect, hp, if_neg,
      Finset.mem_symmDiff, not_false_eq_true, and_true]
    tauto


end
end StatMech.Ising
