/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAtoms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitWeight.Part2
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAtoms
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaCollisionSplitMultiplicity
    (G : SimpleGraph V) (sites : I -> V)
    (m K : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Nat :=
  ∏ e ∈ (lpReplicaCurrentGraph G sites).edgeFinset,
    Nat.choose
      ((ofEdgeFun (lpReplicaCurrentGraph G sites) m) e)
      ((ofEdgeFun (lpReplicaCurrentGraph G sites) K) e)


noncomputable def lpReplicaOrbitConfigurationMultiplicity
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (x : LPReplicaOrbitConfiguration G sites A B q) : Nat :=
  lpReplicaCollisionSplitMultiplicity G sites x.1.1 x.2.1.1 *
    lpReplicaProfileOrbitMultiplicity G sites q x.1.1


end
end StatMech.Ising
