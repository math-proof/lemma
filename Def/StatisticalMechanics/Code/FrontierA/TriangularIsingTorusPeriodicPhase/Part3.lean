/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusBaseSpin
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPeriodicPhase.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Onsager.BaseCase

def triangularOutsideConnector (dx dy top : Int) : List (Fin 6) :=
  (ons_outsideConnector dx dy top).map triangularAxisDirection

end StatMech.FrontierA
