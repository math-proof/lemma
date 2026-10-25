/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessOffCentre.Part4
import Theorem.StatisticalMechanics.Code.OSSS.BetaThresholdBound
import Theorem.StatisticalMechanics.Code.OSSS.LogCesaroLimit.Part2
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

noncomputable def hexagonalNormalizedTheta
    (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  hexagonalOuterInnerTheta q beta n / hexagonalSharpConstant beta0

noncomputable def hexagonalNormalizedThetaPrime
    (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  hexagonalOuterInnerThetaPrime n q beta / hexagonalSharpConstant beta0

noncomputable def hexagonalThresholdTheta
    (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  if beta <= 0 then
    if n = 0 then 1 / hexagonalSharpConstant beta0 else 0
  else hexagonalNormalizedTheta q beta0 n beta

end StatMech.FK.PeriodicPlanar
