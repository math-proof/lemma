/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/HeatFundamental.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ParametricIntegral

open Set MeasureTheory Filter Topology Real

noncomputable section

namespace HeatFundamental

/-- The squared Euclidean norm $|x|^2 = \sum_{i=1}^n (x^i)^2$ of a vector $x \in \mathbb{R}^n$. -/
def euclidNormSq {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 2

/-- Definition 1.0.1: the fundamental solution of the heat equation
$\Gamma_D(t, x) = \frac{1}{(4\pi D t)^{n/2}} \exp\!\left(-\frac{|x|^2}{4Dt}\right)$
for $t > 0$ and $x \in \mathbb{R}^n$. -/
def heatKernel {n : ℕ} (D : ℝ) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  1 / (4 * π * D * t) ^ ((n : ℝ) / 2) * exp (-(euclidNormSq x) / (4 * D * t))

/-- Definition 1.0.2: the Dirac delta distribution acting on a test function $\phi$ by
$\langle \delta, \phi \rangle := \phi(0)$. -/
def deltaDistribution {n : ℕ} (φ : (Fin n → ℝ) → ℝ) : ℝ := φ 0

/-- The Laplacian $\Delta f(x) = \sum_{i=1}^n \partial_i^2 f(x)$ of a real-valued function
on $\mathbb{R}^n$, expressed via iterated Fréchet derivatives in the coordinate directions. -/
def laplacian {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single i 1)

/-- The heat operator $u_t - D\,\Delta u$ acting on a time-dependent function
$u : \mathbb{R} \to (\mathbb{R}^n \to \mathbb{R})$ at $(t, x)$. -/
def heatOperator {n : ℕ} (D : ℝ) (u : ℝ → (Fin n → ℝ) → ℝ) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  deriv (fun s => u s x) t - D * laplacian (u t) x

/-- Total thermal energy at time $t$:
$\mathcal{T}(t) := \int_{\mathbb R^n} u(t, x)\,d^n x$. -/
def totalThermalEnergy {n : ℕ} (u : ℝ → (Fin n → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ x : Fin n → ℝ, u t x

/-- If the surface integral of $\|\nabla f\|$ over the sphere of radius $R$ tends to $0$ as
$R \to \infty$, then $\int_{\mathbb R^n} \Delta f = 0$ (divergence theorem in the limit). -/
def cauchySolution {n : ℕ} (D : ℝ) (g : (Fin n → ℝ) → ℝ) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y, g y * heatKernel D t (x - y)
