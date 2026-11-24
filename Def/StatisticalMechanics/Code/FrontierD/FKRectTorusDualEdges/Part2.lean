module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDualEdges.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectEdgeDualEquiv (R : FKRectTorus) : R.EdgeIndex ≃ R.EdgeIndex where
  toFun := fkRectEdgeToDualEdge R
  invFun := fkRectDualEdgeToEdge R
  left_inv := fkRectDualEdgeToEdge_edgeToDualEdge R
  right_inv := fkRectEdgeToDualEdge_dualEdgeToEdge R

end
end StatMech.FrontierD
