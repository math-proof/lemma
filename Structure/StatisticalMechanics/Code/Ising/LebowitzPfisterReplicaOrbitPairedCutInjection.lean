/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part8
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutHallExact
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagProjection
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

structure LPReplicaOffdiagCoupledPairedCrossToggleInjection
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  selector : LPReplicaOffdiagDecoratedSource G sites i j q ->
    Finset (LPReplicaOrbitCommonSlot G sites q)
  output : LPReplicaOffdiagDecoratedSource G sites i j q ->
    LPReplicaOffdiagDecoratedTarget G sites i j q
  output_valid : forall z,
    LPReplicaOffdiagCoupledPairedOutput G sites i j q (output z)
  output_state : forall z,
    (lpReplicaOffdiagDecoratedTargetBranchedSlotState
      G sites i j q (output z)).2 =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q (selector z)
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
  collision_stable : forall z w,
    output z = output w -> selector z = selector w


end
end StatMech.Ising
