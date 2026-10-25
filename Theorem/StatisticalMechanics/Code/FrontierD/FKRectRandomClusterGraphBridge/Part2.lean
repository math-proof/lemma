/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectEdgeToGraphEdge_bijective (R : FKRectTorus) :
    Function.Bijective (fkRectEdgeToGraphEdge R) := by
  constructor
  · intro a b h
    apply fkRectTorusIndexedEdge_injective R
    exact congrArg Subtype.val h
  · rintro ⟨e, he⟩
    obtain ⟨a, ha⟩ := (mem_fkRectTorusGraph_edgeSet_iff R e).1 he
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha


end
end StatMech.FrontierD
