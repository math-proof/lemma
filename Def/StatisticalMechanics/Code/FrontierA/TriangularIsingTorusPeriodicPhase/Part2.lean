/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusBaseSpin
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPeriodicPhase
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Onsager.BaseCase

def triangularAxisDirection : Fin 4 -> Fin 6 := ![1, 3, 0, 2]

end StatMech.FrontierA
