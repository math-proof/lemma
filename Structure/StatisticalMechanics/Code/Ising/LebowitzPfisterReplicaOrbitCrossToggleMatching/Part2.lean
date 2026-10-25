/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part21
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part7
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

structure LPReplicaOffdiagCrossToggleSelector
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  selector : LPReplicaOffdiagDecoratedSource G sites i j q ->
    Finset (LPReplicaOrbitCommonSlot G sites q)
  output : LPReplicaOffdiagDecoratedSource G sites i j q ->
    LPReplicaOffdiagDecoratedTarget G sites i j q
  output_mem : forall z,
    output z ∈ lpReplicaOffdiagBalancedOutputs G sites i j q
  output_state : forall z,
    (lpReplicaOffdiagDecoratedTargetBranchedSlotState
      G sites i j q (output z)).2 =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q (selector z)
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
  collision_stable : forall z w,
    output z = output w -> selector z = selector w


structure LPReplicaOffdiagCrossToggleMatching
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  output : LPReplicaOffdiagDecoratedSource G sites i j q ->
    LPReplicaOffdiagDecoratedTarget G sites i j q
  output_mem : forall z,
    output z ∈ lpReplicaOffdiagBalancedOutputs G sites i j q
  output_injective : Function.Injective output
  realizes : forall z,
    ∃ P : Finset (LPReplicaOrbitCommonSlot G sites q),
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q (output z)).2 =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q P
          (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)


end
end StatMech.Ising
