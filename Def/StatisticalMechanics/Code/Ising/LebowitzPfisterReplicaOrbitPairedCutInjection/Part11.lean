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
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection.Part11
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def
    lpReplicaOffdiagDecoratedOrbitInjectionOfFixedMaskTargetRealizations
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (hrealize : forall z : LPReplicaOffdiagDecoratedSource G sites i j q,
      ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q P
            (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
    LPReplicaOffdiagDecoratedOrbitInjection G sites i j q := by
  let move : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q :=
    fun z => Classical.choose (hrealize z)
  refine ⟨move, ?_⟩
  intro z w hmove
  apply lpReplicaOffdiagDecoratedSourceSlotState_injective G sites i j q
  apply (lpReplicaOrbitFourColorSlotCrossToggle_involutive
    G sites q P).injective
  have htarget : Classical.choose (hrealize z) =
      Classical.choose (hrealize w) := by
    simpa only [move] using hmove
  rw [← (Classical.choose_spec (hrealize z)),
    ← (Classical.choose_spec (hrealize w)), htarget]


end
end StatMech.Ising
