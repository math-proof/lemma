/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part3
open Finset SimpleGraph

set_option maxHeartbeats 800000


namespace StatMech.FrontierD

noncomputable section

open StatMech

def fkRectGraphForceOpen (R : FKRectTorus)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (eta : FKRectGraphConfiguration R) : FKRectGraphConfiguration R :=
  fun e => if e ∈ I then true else eta e

end
end StatMech.FrontierD
