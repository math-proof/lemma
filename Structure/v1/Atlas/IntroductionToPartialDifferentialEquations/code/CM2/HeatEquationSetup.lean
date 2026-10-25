/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM2/HeatEquationSetup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Trigonometric
open MeasureTheory Real Finset BigOperators
open scoped ENNReal


noncomputable section

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
