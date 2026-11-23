/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/WaveDalembert.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM11.Wave1D
public import Theorem.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM11.Wave1D

@[expose] public section

open Real Set MeasureTheory intervalIntegral


noncomputable section

namespace CM9.Wave

/-- **d'Alembert's formula** for the $1{+}1$ wave equation with initial data
$u(0, x) = f(x)$, $u_t(0, x) = g(x)$:
$$u(t, x) = \tfrac{1}{2} (f(x + t) + f(x - t)) + \tfrac{1}{2} \int_{x - t}^{x + t}
g(z) \, dz.$$ -/
def dAlembertFormula (f g : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (1/2) * (f (x + t) + f (x - t)) + (1/2) * ∫ z in (x - t)..(x + t), g z

end CM9.Wave
end
