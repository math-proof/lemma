/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDualEdges.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectDualEdgeToEdge_edgeToDualEdge
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectDualEdgeToEdge R (fkRectEdgeToDualEdge R e) = e := by
  rcases e with ⟨b, x, y⟩
  cases b
  · simp [fkRectEdgeToDualEdge, fkRectDualEdgeToEdge,
      finitePeriodicSucc_cyclicPred]
  · rfl

@[simp] theorem fkRectEdgeToDualEdge_dualEdgeToEdge
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectEdgeToDualEdge R (fkRectDualEdgeToEdge R e) = e := by
  rcases e with ⟨b, x, y⟩
  cases b
  · rfl
  · simp [fkRectEdgeToDualEdge, fkRectDualEdgeToEdge,
      svCyclicPred_finitePeriodicSucc]


end
end StatMech.FrontierD
