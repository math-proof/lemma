/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM2/HeatEquationSetup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.Trigonometric
open MeasureTheory Real Finset BigOperators
open scoped ENNReal


public noncomputable section

namespace HeatEquation

/-- Data for the 1-dimensional Dirichlet problem for the heat equation
on a rod of length $L$ over the time interval $[0, T]$: diffusion constant $D > 0$,
internal forcing $f(t, x)$, initial profile $g(x)$, and boundary data
$h_0(t), h_L(t)$ at $x = 0$ and $x = L$ respectively. -/
structure DirichletHeatProblem1D where
  L : ℝ
  T : ℝ
  D : ℝ
  g : ℝ → ℝ
  h₀ : ℝ → ℝ
  hL : ℝ → ℝ
  f : ℝ → ℝ → ℝ
  hL_pos : L > 0
  hT_pos : T > 0
  hD_pos : D > 0

end HeatEquation
end
