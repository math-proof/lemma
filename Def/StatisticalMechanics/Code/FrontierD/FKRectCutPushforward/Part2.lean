/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward
open Finset SimpleGraph

set_option maxHeartbeats 800000


namespace StatMech.FrontierD

noncomputable section

open StatMech

def fkRectGraphCriticalEventMass
    (R : FKRectTorus) (q : Real)
    (A : Set (FKRectGraphConfiguration R)) : Real :=
  ∑ eta : FKRectGraphConfiguration R,
    A.indicator
      (fun eta => fkRectGraphCriticalRandomClusterProb R q eta) eta

end
end StatMech.FrontierD
