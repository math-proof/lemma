/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.Part6
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaRowTagEquivFin4_symm_rowToggleFin4_snd
    (a : Fin 4) :
    (lpReplicaRowTagEquivFin4.symm (lpReplicaRowToggleFin4 a)).2 =
      (lpReplicaRowTagEquivFin4.symm a).2 := by
  fin_cases a <;> rfl


theorem lpReplicaOrbitFourColorSlotCrossToggle_current
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q)
    (x : LPReplicaOrbitCommonSlot G sites q) :
    (lpReplicaRowTagEquivFin4.symm
      ((lpReplicaOrbitFourColorSlotCrossToggle G sites q P s).color
        ⟨x, Finset.mem_univ _⟩)).2 =
      (lpReplicaRowTagEquivFin4.symm
        (s.color ⟨x, Finset.mem_univ _⟩)).2 := by
  change (lpReplicaRowTagEquivFin4.symm
      (if x ∈ P then lpReplicaRowToggleFin4
          (s.color ⟨x, Finset.mem_univ _⟩)
        else s.color ⟨x, Finset.mem_univ _⟩)).2 = _
  by_cases hx : x ∈ P
  · simp [hx]
  · simp [hx]


end
end StatMech.Ising
