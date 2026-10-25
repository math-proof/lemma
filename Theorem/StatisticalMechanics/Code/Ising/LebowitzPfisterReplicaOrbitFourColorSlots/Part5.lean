/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem card_lpReplicaOrbitCommonSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOrbitCommonSlot G sites q) =
      (∑ e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites), q e.1 / 2) +
        ∑ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites), q e.1 := by
  unfold LPReplicaOrbitCommonSlot
  calc
    _ = Fintype.card
          (Σ e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites), Fin (q e.1 / 2)) +
        Fintype.card
          (Σ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites), Fin (q e.1)) :=
      Fintype.card_sum
    _ = _ := by
      rw [Fintype.card_sigma, Fintype.card_sigma]
      simp


end
end StatMech.Ising
