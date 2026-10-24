/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierTransform.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
open MeasureTheory Complex Finset SchwartzMap
open scoped FourierTransform RealInnerProductSpace

set_option maxHeartbeats 400000

noncomputable section

namespace FourierAnalysis

/-- A multi-index of dimension `n`: an `n`-tuple $\vec{\alpha} = (\alpha^1, \dots, \alpha^n)$
of non-negative integers, encoded as a function `Fin n → ℕ`. -/
abbrev MultiIndex (n : ℕ) := Fin n → ℕ

/-- The order of a multi-index $\vec{\alpha}$: $|\vec{\alpha}| := \alpha^1 + \cdots + \alpha^n$. -/
def MultiIndex.order {n : ℕ} (α : MultiIndex n) : ℕ := ∑ i, α i

/-- The monomial $x^{\vec{\alpha}} := (x^1)^{\alpha^1} \cdots (x^n)^{\alpha^n}$ for
$x \in \mathbb{C}^n$ and multi-index $\vec{\alpha}$. -/
noncomputable def multiIndexMonomial {n : ℕ} (x : Fin n → ℂ) (α : MultiIndex n) : ℂ :=
  ∏ i, x i ^ α i

/-- The `k`-fold partial derivative of `f` with respect to the `i`-th coordinate,
$\partial_i^k f$, defined by iterating one-variable differentiation along the `i`-th axis. -/
noncomputable def iteratedPartialDeriv {n : ℕ} (i : Fin n) (k : ℕ)
    (f : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  (fun g x => deriv (fun t => g (Function.update x i t)) (x i))^[k] f

/-- The differential operator $\partial_{\vec{\alpha}} := \partial_1^{\alpha^1} \cdots
\partial_n^{\alpha^n}$ associated to a multi-index $\vec{\alpha}$. -/
noncomputable def multiIndexDeriv {n : ℕ} (α : MultiIndex n)
    (f : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  (List.finRange n).foldl (fun g i => iteratedPartialDeriv i (α i) g) f

/-- The space $C^k$: predicate that `f : ℝ^n → ℂ` is `k`-times continuously differentiable. -/
def IsCk (n : ℕ) (k : ℕ) (f : (Fin n → ℝ) → ℂ) : Prop :=
  ContDiff ℝ k f

/-- The space $C_0$: predicate that `f : ℝ^n → ℂ` is continuous and vanishes at infinity,
i.e. $\lim_{|x| \to \infty} f(x) = 0$. -/
def IsC0 (n : ℕ) (f : (Fin n → ℝ) → ℂ) : Prop :=
  Continuous f ∧ Filter.Tendsto (fun x => ‖f x‖) (Filter.cocompact (Fin n → ℝ)) (nhds 0)

/-- The supremum norm $\|f\|_{C_0} := \sup_{x \in \mathbb{R}^n} |f(x)|$. -/
noncomputable def supNorm (n : ℕ) (f : (Fin n → ℝ) → ℂ) : ℝ :=
  ⨆ x, ‖f x‖

/-- The one-dimensional Fourier transform
$\hat{f}(\xi) := \int_{\mathbb{R}} f(x) e^{-2\pi i \xi x}\, dx$. -/
def fourierTransform (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, f x * exp (↑(-2 * Real.pi * ξ * x) * I)

/-- The one-dimensional inverse Fourier transform
$f^{\vee}(x) := \int_{\mathbb{R}} f(\xi) e^{2\pi i \xi x}\, d\xi$. -/
def inverseFourierTransform (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ ξ : ℝ, f ξ * exp (↑(2 * Real.pi * ξ * x) * I)

/-- The complex $L^2$ inner product on $\mathbb{R}$:
$\langle f, g \rangle := \int_{\mathbb{R}} f(x) \overline{g(x)}\, dx$. -/
def complexL2Inner (f g : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ, f x * starRingEnd ℂ (g x)

/-- The complex $L^2$ norm on $\mathbb{R}$: $\|f\| := \langle f, f \rangle^{1/2}$. -/
def complexL2Norm (f : ℝ → ℂ) : ℝ :=
  Real.sqrt (Complex.re (complexL2Inner f f))

/-- The complex $L^2$ inner product on $\mathbb{R}^n$:
$\langle f, g \rangle := \int_{\mathbb{R}^n} f(x) \overline{g(x)}\, d^n x$. -/
def complexL2InnerND {n : ℕ} (f g : (Fin n → ℝ) → ℂ) : ℂ :=
  ∫ x, f x * starRingEnd ℂ (g x)

/-- The complex $L^2$ norm on $\mathbb{R}^n$: $\|f\| := \langle f, f \rangle^{1/2}$. -/
def complexL2NormND {n : ℕ} (f : (Fin n → ℝ) → ℂ) : ℝ :=
  Real.sqrt (Complex.re (complexL2InnerND f f))

/-- Translation of a function on $\mathbb{R}$ by `y`: $(\tau_y f)(x) := f(x - y)$. -/
def translate (y : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun x => f (x - y)

/-- The complex convolution on $\mathbb{R}$: $(f * g)(x) := \int_{\mathbb{R}} f(x - y) g(y)\, dy$. -/
def complexConvolution (f g : ℝ → ℂ) : ℝ → ℂ := fun x =>
  ∫ y : ℝ, f (x - y) * g y

/-- The complex convolution on $\mathbb{R}^n$:
$(f * g)(x) := \int_{\mathbb{R}^n} f(y) g(x - y)\, d^n y$. -/
def complexConvolutionND {n : ℕ}
    (f g : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  ∫ y : Fin n → ℝ, f y * g (x - y)

/-- The $n$-dimensional Fourier transform
$\hat{f}(\xi) := \int_{\mathbb{R}^n} f(x) e^{-2\pi i \xi \cdot x}\, d^n x$. -/
def fourierTransformND (n : ℕ) (f : (Fin n → ℝ) → ℂ) (ξ : Fin n → ℝ) : ℂ :=
  ∫ x, f x * Complex.exp (↑(-2 * Real.pi) * Complex.I * ↑(∑ j, ξ j * x j))

/-- The $n$-dimensional inverse Fourier transform
$g^{\vee}(x) := \int_{\mathbb{R}^n} g(\xi) e^{2\pi i \xi \cdot x}\, d^n \xi$. -/
def inverseFourierTransformND (n : ℕ) (g : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  ∫ ξ, g ξ * Complex.exp (↑(2 * Real.pi) * Complex.I * ↑(∑ j, ξ j * x j))

/-- The squared Euclidean norm $|x|^2 := \sum_i (x_i)^2$ on $\mathbb{R}^n$. -/
def euclidNormSq {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 2

/-- Translation in $\mathbb{R}^n$: $(\tau_y f)(x) := f(x - y)$ (Definition 2.0.6). -/
def translateFn {n : ℕ} (y : Fin n → ℝ) (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  f (x - y)

/-- Auxiliary 1D operator: $(\text{mulByPoly}\, f\, k)(x) := (-2\pi i x)^k\, f(x)$. -/
noncomputable def mulByPoly (f : ℝ → ℂ) (k : ℕ) : ℝ → ℂ :=
  fun x => (↑(-2 * Real.pi) * I * ↑x) ^ k * f x
