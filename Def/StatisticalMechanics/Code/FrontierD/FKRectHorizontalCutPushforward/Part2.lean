/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCutPushforward
open Finset


namespace StatMech.FrontierD

noncomputable section

def fkRectCriticalHorizontalCutEventMass
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) : Real :=
  fkRectCriticalEventMass R q
      {eta | FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A} /
    fkRectCriticalClosedMass R q (fkRectHorizontalCutEdges R)

end
end StatMech.FrontierD
