/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part21
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagCrossToggleMaskRelated_iff_crossTrace
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    LPReplicaOffdiagCrossToggleMaskRelated G sites i j q z y ↔
      y ∈ lpReplicaOffdiagBalancedOutputs G sites i j q ∧
        lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y =
          lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z := by
  unfold LPReplicaOffdiagCrossToggleMaskRelated
    lpReplicaOffdiagDecoratedTargetCrossTrace
    lpReplicaOffdiagDecoratedSourceCrossTrace
  rw [exists_crossToggle_eq_iff_crossNormalize_eq]


end
end StatMech.Ising
