/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part21
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaOffdiagCrossToggleMaskNeighbors
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact Finset.univ.filter fun y =>
    LPReplicaOffdiagCrossToggleMaskRelated G sites i j q z y


noncomputable def LPReplicaOffdiagCrossToggleMaskHall
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop := by
  classical
  exact forall S : Finset (LPReplicaOffdiagDecoratedSource G sites i j q),
    S.card <= (S.biUnion
      (lpReplicaOffdiagCrossToggleMaskNeighbors G sites i j q)).card


noncomputable def lpReplicaOffdiagDecoratedSourceCrossTraceFiber
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact Finset.univ.filter fun z =>
    lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z = u


noncomputable def lpReplicaOffdiagBalancedOutputCrossTraceFiber
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact (lpReplicaOffdiagBalancedOutputs G sites i j q).filter fun y =>
    lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y = u


noncomputable def lpReplicaOffdiagDecoratedSourceCrossTraceMasks
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (Finset (LPReplicaOrbitCommonSlot G sites q)) := by
  classical
  exact (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
    G sites i j q u).image fun z =>
      lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)


noncomputable def lpReplicaOffdiagBalancedOutputCrossTraceBranchedMasks
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (Bool × Finset (LPReplicaOrbitCommonSlot G sites q)) := by
  classical
  exact (lpReplicaOffdiagBalancedOutputCrossTraceFiber
    G sites i j q u).image fun y =>
      ((lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).1,
        lpReplicaOrbitFourColorSlotRowMask G sites q
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2)


end
end StatMech.Ising
