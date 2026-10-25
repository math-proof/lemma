/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCollisionResummation.Part4
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaCollision_projection
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) (ha : a <= m) :
    (fun e => a e + lpReplicaReflectedResidual G sites m a
      (lpReplicaCurrentEdgeReflect G sites e)) = m := by
  funext e
  rw [lpReplicaReflectedResidual, lpReplicaCurrentEdgeReflect_involutive]
  exact Nat.add_sub_cancel' (ha e)


end
end StatMech.Ising
