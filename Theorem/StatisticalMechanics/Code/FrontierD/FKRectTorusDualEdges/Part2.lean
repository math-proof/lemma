/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDualEdges.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part2


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectEdgeDualEquiv_apply
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectEdgeDualEquiv R e = fkRectEdgeToDualEdge R e := rfl

@[simp] theorem fkRectEdgeDualEquiv_symm_apply
    (R : FKRectTorus) (e : R.EdgeIndex) :
    (fkRectEdgeDualEquiv R).symm e = fkRectDualEdgeToEdge R e := rfl


end
end StatMech.FrontierD
