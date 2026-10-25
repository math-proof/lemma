/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectEdgeToGraphEdge (R : FKRectTorus) (a : R.EdgeIndex) :
    {e // e ∈ (fkRectTorusGraph R).edgeSet} :=
  ⟨fkRectTorusIndexedEdge R a,
    (mem_fkRectTorusGraph_edgeSet_iff R _).2 ⟨a, rfl⟩⟩

end
end StatMech.FrontierD
