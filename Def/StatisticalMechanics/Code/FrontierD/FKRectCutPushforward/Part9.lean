/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part8
open Finset SimpleGraph

set_option maxHeartbeats 800000


namespace StatMech.FrontierD

noncomputable section

open StatMech

def fkRectCriticalCutFreeEventMass
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) : Real :=
  fkRectCriticalEventMass R q
      {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A} /
    fkRectCriticalClosedMass R q (fkRectTorusCutEdges R)

end
end StatMech.FrontierD
