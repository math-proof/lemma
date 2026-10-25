/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardFormanProduct
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part4


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V E D Q : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]
  [Fintype Q] [DecidableEq Q]


noncomputable def criticalKacWardRibbonPrefactor
    (thetaEdge : E -> Real) (exceptional : V -> Bool) : Complex :=
  (-1 : Complex) ^ Fintype.card V *
    kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
    (∏ v : V, coneQuarterPhase exceptional v) *
    kwLaplacianEdgePrefactor thetaEdge


end StatMech.FrontierA
