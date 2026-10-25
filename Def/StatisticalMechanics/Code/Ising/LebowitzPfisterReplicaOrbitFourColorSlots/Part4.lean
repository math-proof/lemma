/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def LPReplicaOrbitProfileCopyCoord
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Σ c : ↑(lpReplicaCurrentEdgeOrbitFixed G sites) ⊕
      (↑(lpReplicaCurrentEdgeOrbitStrictReps G sites) ⊕
        ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)),
    Fin (m ((lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm c))


noncomputable def lpReplicaProfileCopyEquivOrbitCoord
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) m ≃
      LPReplicaOrbitProfileCopyCoord G sites m :=
  Equiv.sigmaCongr (lpReplicaCurrentEdgeOrbitCoordEquiv G sites) fun e =>
    Equiv.cast (congrArg Fin (congrArg m
      ((lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm_apply_apply e).symm))


end
end StatMech.Ising
