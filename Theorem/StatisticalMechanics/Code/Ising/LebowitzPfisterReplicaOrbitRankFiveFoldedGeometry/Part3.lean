/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateResidual.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaCurrentFoldedEdge_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset) :
    lpReplicaCurrentFoldedEdge G sites
        (lpReplicaCurrentEdgeReflect G sites e) =
      lpReplicaCurrentFoldedEdge G sites e := by
  unfold lpReplicaCurrentFoldedEdge
  rw [lpReplicaCurrentEdgeReflect_val, Sym2.map_map]
  apply Sym2.map_congr
  intro x _
  exact lpReplicaCurrentFold_reflect x


end
end StatMech.Ising
