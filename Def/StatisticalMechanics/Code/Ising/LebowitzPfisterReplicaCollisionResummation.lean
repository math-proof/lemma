/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCollisionResummation
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaCurrentEdgeReflect (G : SimpleGraph V) (sites : I -> V) :
    Equiv.Perm (lpReplicaCurrentGraph G sites).edgeFinset where
  toFun e := ⟨Sym2.map lpReplicaCurrentReflect e.1, by
    rcases e with ⟨e, he⟩
    induction e with
    | h x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rw [SimpleGraph.mem_edgeFinset]
      change Sym2.map lpReplicaCurrentReflect s(x, y) ∈
        (lpReplicaCurrentGraph G sites).edgeSet
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
      exact (lpReplicaCurrentGraph_adj_reflect G sites x y).2 he⟩
  invFun e := ⟨Sym2.map lpReplicaCurrentReflect e.1, by
    rcases e with ⟨e, he⟩
    induction e with
    | h x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rw [SimpleGraph.mem_edgeFinset]
      change Sym2.map lpReplicaCurrentReflect s(x, y) ∈
        (lpReplicaCurrentGraph G sites).edgeSet
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
      exact (lpReplicaCurrentGraph_adj_reflect G sites x y).2 he⟩
  left_inv := by
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
  right_inv := by
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
