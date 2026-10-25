/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalFullGraphLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFKG.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigEventLaw.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech

instance fkRectCriticalFullGraphDecidableRel (R : FKRectTorus) :
    DecidableRel (fkRectTorusGraph R).Adj := Classical.decRel _


end
end StatMech.FrontierD
