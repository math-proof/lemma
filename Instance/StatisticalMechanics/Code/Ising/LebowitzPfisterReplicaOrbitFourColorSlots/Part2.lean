module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
public import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part5
open Finset
open scoped symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable instance instFintypeLPReplicaOrbitCommonSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaOrbitCommonSlot G sites q) := by
  unfold LPReplicaOrbitCommonSlot
  infer_instance

noncomputable instance instDecidableEqLPReplicaOrbitCommonSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    DecidableEq (LPReplicaOrbitCommonSlot G sites q) :=
  Classical.decEq _


end
end StatMech.Ising
