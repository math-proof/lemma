module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGenericShear.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleHomotopy.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardShearPhaseHomotopy


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardShearPhaseHomotopy.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open scoped BigOperators

open Set

noncomputable def kwDoubleShearLinearEquiv (tx ty t : ℝ) : ℂ ≃ₗ[ℝ] ℂ :=
  (kwShearXLinearEquiv (t * tx)).trans (kwShearYLinearEquiv (t * ty))

end StatMech.FrontierA
