/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part9
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOrbitFourColorSlotRowToggle_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q)) :
    Function.Involutive
      (lpReplicaOrbitFourColorSlotRowToggle G sites q P) := by
  intro s
  apply LPReplicaOrbitFourColorSlotState.ext
  · rfl
  · funext x
    change (if x.1 ∈ P then
        lpReplicaRowToggleFin4
          (if x.1 ∈ P then lpReplicaRowToggleFin4 (s.color x)
            else s.color x)
      else if x.1 ∈ P then lpReplicaRowToggleFin4 (s.color x)
        else s.color x) = s.color x
    by_cases hx : x.1 ∈ P
    · rw [if_pos hx, if_pos hx]
      exact lpReplicaRowToggleFin4_involutive (s.color x)
    · rw [if_neg hx, if_neg hx]


end
end StatMech.Ising
