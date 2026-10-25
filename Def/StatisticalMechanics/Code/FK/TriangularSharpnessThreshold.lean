/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessOffCentre.Part4
import Theorem.StatisticalMechanics.Code.OSSS.BetaThresholdBound
import Theorem.StatisticalMechanics.Code.OSSS.LogCesaroLimit.Part2
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

noncomputable def triangularNormalizedTheta
    (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  triangularOuterInnerTheta q beta n / triangularSharpConstant beta0

noncomputable def triangularNormalizedThetaPrime
    (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  triangularOuterInnerThetaPrime n q beta / triangularSharpConstant beta0

noncomputable def triangularThresholdTheta
    (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  if beta <= 0 then
    if n = 0 then 1 / triangularSharpConstant beta0 else 0
  else triangularNormalizedTheta q beta0 n beta

end StatMech.FK.PeriodicPlanar
