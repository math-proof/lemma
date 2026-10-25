/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCardinality.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRepresentatives.Part2
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem mem_lpReplicaCurrentEdgeOrbitReps
    (G : SimpleGraph V) (sites : I -> V)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset) :
    e ∈ lpReplicaCurrentEdgeOrbitReps G sites ↔
      lpReplicaCurrentEdgeRank G sites e <=
        lpReplicaCurrentEdgeRank G sites
          (lpReplicaCurrentEdgeReflect G sites e) := by
  classical
  simp [lpReplicaCurrentEdgeOrbitReps]


theorem lpReplicaCurrentEdge_mem_reps_or_reflect_mem_reps
    (G : SimpleGraph V) (sites : I -> V)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset) :
    e ∈ lpReplicaCurrentEdgeOrbitReps G sites ∨
      lpReplicaCurrentEdgeReflect G sites e ∈
        lpReplicaCurrentEdgeOrbitReps G sites := by
  rw [mem_lpReplicaCurrentEdgeOrbitReps,
    mem_lpReplicaCurrentEdgeOrbitReps]
  rcases le_total (lpReplicaCurrentEdgeRank G sites e)
      (lpReplicaCurrentEdgeRank G sites
        (lpReplicaCurrentEdgeReflect G sites e)) with h | h
  · exact Or.inl h
  · right
    convert h using 1
    exact congrArg (lpReplicaCurrentEdgeRank G sites)
      (lpReplicaCurrentEdgeReflect_involutive G sites e)


theorem lpReplicaCurrentEdge_eq_reflect_of_mem_reps_of_reflect_mem_reps
    (G : SimpleGraph V) (sites : I -> V)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset)
    (he : e ∈ lpReplicaCurrentEdgeOrbitReps G sites)
    (hre : lpReplicaCurrentEdgeReflect G sites e ∈
      lpReplicaCurrentEdgeOrbitReps G sites) :
    e = lpReplicaCurrentEdgeReflect G sites e := by
  rw [mem_lpReplicaCurrentEdgeOrbitReps] at he hre
  rw [lpReplicaCurrentEdgeReflect_involutive] at hre
  apply lpReplicaCurrentEdgeRank_injective G sites
  exact le_antisymm he hre


theorem lpReplicaCurrentEdge_mem_reps_iff_reflect_not_mem_reps_of_ne
    (G : SimpleGraph V) (sites : I -> V)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset)
    (hne : e ≠ lpReplicaCurrentEdgeReflect G sites e) :
    e ∈ lpReplicaCurrentEdgeOrbitReps G sites ↔
      lpReplicaCurrentEdgeReflect G sites e ∉
        lpReplicaCurrentEdgeOrbitReps G sites := by
  constructor
  · intro he hre
    exact hne
      (lpReplicaCurrentEdge_eq_reflect_of_mem_reps_of_reflect_mem_reps
        G sites e he hre)
  · intro hre
    rcases lpReplicaCurrentEdge_mem_reps_or_reflect_mem_reps G sites e with
      he | he
    · exact he
    · exact False.elim (hre he)


end
end StatMech.Ising
