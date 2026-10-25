/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part5
open Finset SimpleGraph

set_option maxHeartbeats 800000


namespace StatMech.FrontierD

noncomputable section

open StatMech

def fkRectForceEdgesOpen (R : FKRectTorus)
    (I : Finset R.EdgeIndex) (omega : R.Configuration) : R.Configuration :=
  fun a => if a ∈ I then true else omega a

end
end StatMech.FrontierD
