module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFourSignMajority
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardInteriorSideSplice
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
public import Mathlib.Data.List.Rotate
public import Def.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

theorem kwVectorTurnPhase_ne_zero (x y : ℂ) :
    kwVectorTurnPhase x y ≠ 0 := by
  unfold kwVectorTurnPhase kwAngleTurnPhase
  exact Complex.exp_ne_zero _


end StatMech.FrontierA
