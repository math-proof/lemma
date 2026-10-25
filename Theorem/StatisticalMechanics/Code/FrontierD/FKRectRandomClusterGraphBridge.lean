/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem mem_fkRectTorusGraph_edgeSet_iff (R : FKRectTorus)
    (e : Sym2 R.Vertex) :
    e ∈ (fkRectTorusGraph R).edgeSet ↔
      ∃ a : R.EdgeIndex, fkRectTorusIndexedEdge R a = e := by
  obtain ⟨⟨x, y⟩, rfl⟩ := Quot.exists_rep e
  rw [SimpleGraph.mem_edgeSet]
  rfl


end
end StatMech.FrontierD
