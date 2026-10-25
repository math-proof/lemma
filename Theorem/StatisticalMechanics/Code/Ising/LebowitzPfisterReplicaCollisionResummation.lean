/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCollisionResummation
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaCurrentEdgeReflect_val
    (G : SimpleGraph V) (sites : I -> V)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset) :
    (lpReplicaCurrentEdgeReflect G sites e).1 =
      Sym2.map lpReplicaCurrentReflect e.1 := rfl

theorem lpReplicaCurrentEdgeReflect_involutive
    (G : SimpleGraph V) (sites : I -> V) :
    Function.Involutive (lpReplicaCurrentEdgeReflect G sites) := by
  intro e
  apply Subtype.ext
  change Sym2.map lpReplicaCurrentReflect
    (Sym2.map lpReplicaCurrentReflect e.1) = e.1
  rw [Sym2.map_map]
  have hf : (lpReplicaCurrentReflect : LPReplicaCurrentVertex V -> _)
      ∘ lpReplicaCurrentReflect = id := by
    funext x
    exact lpReplicaCurrentReflect_involutive x
  rw [hf, Sym2.map_id]
  rfl


end
end StatMech.Ising
