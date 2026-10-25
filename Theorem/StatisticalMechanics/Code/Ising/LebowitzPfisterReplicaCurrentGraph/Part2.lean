/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCurrentGraph.Part2
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaCurrentRel_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (x y : LPReplicaCurrentVertex V) :
    lpReplicaCurrentRel G sites (lpReplicaCurrentReflect x)
        (lpReplicaCurrentReflect y) <->
      lpReplicaCurrentRel G sites x y := by
  rcases x with (x | b) <;> rcases y with (y | c)
  · rcases x with x | x <;> rcases y with y | y <;>
      simp only [lpReplicaCurrentReflect_left, lpReplicaCurrentReflect_right,
        lpReplicaCurrentRel]
  · rcases x with x | x <;> cases c <;>
      simp [lpReplicaCurrentRel]
  · cases b <;> rcases y with y | y <;>
      simp [lpReplicaCurrentRel]
  · cases b <;> cases c <;> simp [lpReplicaCurrentRel]

theorem lpReplicaCurrentGraph_adj_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (x y : LPReplicaCurrentVertex V) :
    (lpReplicaCurrentGraph G sites).Adj
        (lpReplicaCurrentReflect x) (lpReplicaCurrentReflect y) <->
      (lpReplicaCurrentGraph G sites).Adj x y := by
  unfold lpReplicaCurrentGraph
  rw [SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hrel⟩
    refine ⟨fun hxy => hne (congrArg lpReplicaCurrentReflect hxy), ?_⟩
    rcases hrel with hrel | hrel
    · exact Or.inl ((lpReplicaCurrentRel_reflect G sites x y).mp hrel)
    · exact Or.inr ((lpReplicaCurrentRel_reflect G sites y x).mp hrel)
  · rintro ⟨hne, hrel⟩
    refine ⟨lpReplicaCurrentReflect.injective.ne hne, ?_⟩
    rcases hrel with hrel | hrel
    · exact Or.inl ((lpReplicaCurrentRel_reflect G sites x y).mpr hrel)
    · exact Or.inr ((lpReplicaCurrentRel_reflect G sites y x).mpr hrel)


end
end StatMech.Ising
