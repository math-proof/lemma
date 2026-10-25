/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOffdiagSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCutParity.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaBound.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOffdiagSwitching
open Finset
open scoped BigOperators symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaCurrentEdgeFlux_ofEdgeFun
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaCurrentEdgeFlux G sites
      (ofEdgeFun (lpReplicaCurrentGraph G sites) m) = m := by
  funext e
  unfold lpReplicaCurrentEdgeFlux ofEdgeFun
  rw [dif_pos e.2]


end
end StatMech.Ising
