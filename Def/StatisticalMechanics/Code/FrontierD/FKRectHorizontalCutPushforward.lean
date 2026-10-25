/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
open Finset


namespace StatMech.FrontierD

noncomputable section

def fkRectForceHorizontalCutClosed (R : FKRectTorus)
    (omega : R.Configuration) : R.Configuration :=
  fkRectForceEdgesClosed R (fkRectHorizontalCutEdges R) omega


def FKRectHorizontalCutClosedConfiguration
    (R : FKRectTorus) (eta : R.Configuration) : Prop :=
  ∀ a ∈ fkRectHorizontalCutEdges R, eta a = false

end
end StatMech.FrontierD
