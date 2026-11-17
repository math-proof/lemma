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
public import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM2.HeatEquationSetup

@[expose] public section

open MeasureTheory Real Finset BigOperators
open scoped ENNReal


noncomputable section

namespace HeatEquation

/-- The $m$-th Fourier sine coefficient of $f$ on $[0, 1]$:
$A_m = 2 \int_0^1 f(x) \sin(m \pi x)\, dx$. -/
def fourierSineCoeff (f : ℝ → ℝ) (m : ℕ) : ℝ :=
  2 * ∫ x in (0:ℝ)..1, f x * sin (↑m * π * x)

/-- The $N$-th partial Fourier sine series of $f$:
$\sum_{m=1}^N A_m \sin(m \pi x)$. -/
def fourierSinePartialSum (f : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  (Finset.range N).sum fun m =>
    fourierSineCoeff f (m + 1) * sin (↑(m + 1) * π * x)

/-- The squared $L^2([0, 1])$ norm: $\|f\|_{L^2}^2 = \int_0^1 |f(x)|^2\, dx$. -/
def L2NormSq (f : ℝ → ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1, (f x) ^ 2

/-- The squared $L^2([0, 1])$ error between $f$ and its $N$-th Fourier sine partial sum. -/
def L2ErrorSq (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∫ x in (0:ℝ)..1, (f x - fourierSinePartialSum f N x) ^ 2

/-- The $m$-th eigenvalue of $-\partial_x^2$ with Dirichlet conditions on $[0, 1]$:
$-m^2 \pi^2$. -/
def eigenvalue (m : ℕ) : ℝ := -(↑m ^ 2 * π ^ 2)

end HeatEquation
end
