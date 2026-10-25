/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitProfileTransferGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitProfileTransferGraph.Part2


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaCommonOrbitTransferGraph_adj_iff
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (m n : LPReplicaCommonOrbitProfile G sites q) :
    (lpReplicaCommonOrbitTransferGraph G sites q).Adj m n ↔
      m ≠ n ∧ LPReplicaProfilePartialReflects G sites m.1 n.1 := by
  simp only [lpReplicaCommonOrbitTransferGraph, SimpleGraph.top_adj]
  constructor
  · intro hne
    exact ⟨hne,
      lpReplicaProfilePartialReflects_commonOrbit G sites q m n⟩
  · exact And.left

theorem lpReplicaCommonOrbitTransferGraph_preconnected
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaCommonOrbitTransferGraph G sites q).Preconnected := by
  exact SimpleGraph.preconnected_top

theorem lpReplicaCommonOrbitTransferGraph_component_eq
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (m n : LPReplicaCommonOrbitProfile G sites q) :
    (lpReplicaCommonOrbitTransferGraph G sites q).connectedComponentMk m =
      (lpReplicaCommonOrbitTransferGraph G sites q).connectedComponentMk n := by
  exact SimpleGraph.ConnectedComponent.sound
    (lpReplicaCommonOrbitTransferGraph_preconnected G sites q m n)


end
end StatMech.Ising
