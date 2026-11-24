module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFourSignMajority
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardInteriorSideSplice
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
public import Mathlib.Data.List.Rotate
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable def kwVectorPhasePath : List ℂ → ℂ
  | [] => 1
  | [_] => 1
  | x :: y :: tail =>
      kwVectorTurnPhase x y * kwVectorPhasePath (y :: tail)


noncomputable def kwVectorPhaseCycle : List ℂ → ℂ
  | [] => 1
  | x :: tail =>
      kwVectorPhasePath (x :: tail) *
        kwVectorTurnPhase ((x :: tail).getLastD x) x

end StatMech.FrontierA
