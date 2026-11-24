module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardCycleCoefficient.Part5
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable def kwAngleTurnPhase (a b : Real.Angle) : ℂ :=
  Complex.exp ((((b - a).toReal : ℂ) * Complex.I) / 2)


end StatMech.FrontierA
