/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part21
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Abbrev.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagCrossToggleMaskHall_iff_traceFiberEmbeddings
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaOffdiagCrossToggleMaskHall G sites i j q ↔
      forall u : LPReplicaOrbitFourColorSlotState G sites q,
        Nonempty (LPReplicaOffdiagCrossTraceFiberEmbedding
          G sites i j q u) := by
  rw [lpReplicaOffdiagCrossToggleMaskHall_iff_crossTraceFiberCards]
  apply forall_congr'
  intro u
  rw [Function.Embedding.nonempty_iff_card_le]
  simp only [Fintype.card_coe]


end
end StatMech.Ising
