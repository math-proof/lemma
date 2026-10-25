/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFKG.Part2
import Theorem.StatisticalMechanics.Code.FK.CircuitLowerBound.Part6
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech

instance fkRectFiniteEnergyDecidableRel (R : FKRectTorus) :
    DecidableRel (fkRectTorusGraph R).Adj := Classical.decRel _

end
end StatMech.FrontierD
