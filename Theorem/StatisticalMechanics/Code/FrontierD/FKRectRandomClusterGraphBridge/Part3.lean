/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectEdgeGraphEquiv_val (R : FKRectTorus)
    (a : R.EdgeIndex) :
    (fkRectEdgeGraphEquiv R a).1 = fkRectTorusIndexedEdge R a := rfl

@[simp] theorem fkRectEdgeGraphEquiv_symm_indexedEdge
    (R : FKRectTorus)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
    fkRectTorusIndexedEdge R ((fkRectEdgeGraphEquiv R).symm e) = e.1 := by
  have h := (fkRectEdgeGraphEquiv R).apply_symm_apply e
  exact congrArg Subtype.val h


end
end StatMech.FrontierD
