/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFourSignMajority
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardInteriorSideSplice
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
import Mathlib.Data.List.Rotate
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar


namespace StatMech.FrontierA

noncomputable def kwVectorTurnPhase (x y : ℂ) : ℂ :=
  kwAngleTurnPhase (Complex.arg x : Real.Angle)
    (Complex.arg y : Real.Angle)

end StatMech.FrontierA
