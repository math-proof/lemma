/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part8
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaRowToggleFin4_involutive :
    Function.Involutive lpReplicaRowToggleFin4 := by
  intro a
  fin_cases a <;> rfl

@[simp] theorem lpReplicaRowTagEquivFin4_symm_rowToggleFin4_fst
    (a : Fin 4) :
    (lpReplicaRowTagEquivFin4.symm (lpReplicaRowToggleFin4 a)).1 =
      !(lpReplicaRowTagEquivFin4.symm a).1 := by
  fin_cases a <;> rfl


end
end StatMech.Ising
