/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/ConformalSpinFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable def isingSpinScalingDimension : ℝ := 1 / 8


noncomputable def spinDerivativeFactor {ι : Type*} [Fintype ι] (d : ι → ℂ) : ℝ :=
  ∏ i, ‖d i‖ ^ isingSpinScalingDimension


noncomputable def spinConformalFactor {ι : Type*} [Fintype ι]
    (Φ : ℂ → ℂ) (a : ι → ℂ) : ℝ :=
  spinDerivativeFactor fun i => deriv Φ (a i)


end StatMech.FrontierA
