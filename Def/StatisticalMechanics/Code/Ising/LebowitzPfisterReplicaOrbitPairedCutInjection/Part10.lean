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
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection.Part10
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def
    lpReplicaOffdiagCoupledPairedCrossToggleInjectionOfFixedMaskRealizations
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (hrealize : forall z : LPReplicaOffdiagDecoratedSource G sites i j q,
      ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
        LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2 =
            lpReplicaOrbitFourColorSlotCrossToggle G sites q P
              (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
    LPReplicaOffdiagCoupledPairedCrossToggleInjection G sites i j q where
  selector := fun _ => P
  output := fun z => Classical.choose (hrealize z)
  output_valid := fun z => (Classical.choose_spec (hrealize z)).1
  output_state := fun z => (Classical.choose_spec (hrealize z)).2
  collision_stable := by
    intro z w _
    rfl


end
end StatMech.Ising
