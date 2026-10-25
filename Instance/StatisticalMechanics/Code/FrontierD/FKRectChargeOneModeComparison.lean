/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectChargeOneModeComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.BoolModeForcedSum
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

instance medialLoopDecidableEq {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) :
    DecidableEq (FKMedialLoop T pairing) := Classical.decEq _


end
end StatMech.FrontierD
