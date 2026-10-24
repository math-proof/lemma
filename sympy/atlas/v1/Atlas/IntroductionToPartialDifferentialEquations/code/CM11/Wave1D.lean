/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM11/Wave1D.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open Real Set MeasureTheory intervalIntegral

noncomputable section

namespace WaveEquation1D

/-- D'Alembert's formula for the $1+1$ dimensional wave equation:
$u(t,x) = \frac{1}{2}(f(x+t) + f(x-t)) + \frac{1}{2}\int_{x-t}^{x+t} g(z)\,dz$. -/
def dAlembertSolution (f g : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (f (x + t) + f (x - t)) / 2 + (∫ y in (x - t)..(x + t), g y) / 2

/-- The odd extension of a function $f : [0, \infty) \to \mathbb{R}$ to all of $\mathbb{R}$:
$\tilde{f}(y) = f(y)$ for $y \ge 0$, and $\tilde{f}(y) = -f(-y)$ for $y < 0$. -/
def oddExtension (f : ℝ → ℝ) : ℝ → ℝ :=
  fun y => if 0 ≤ y then f y else -(f (-y))

/-- The d'Alembert formula for the half-line wave equation with Dirichlet boundary condition
$u(t, 0) = 0$, obtained by applying d'Alembert's formula to the odd extensions of $f$ and $g$. -/
def dAlembertHalfLine (f g : ℝ → ℝ) (t x : ℝ) : ℝ :=
  dAlembertSolution (oddExtension f) (oddExtension g) t x
