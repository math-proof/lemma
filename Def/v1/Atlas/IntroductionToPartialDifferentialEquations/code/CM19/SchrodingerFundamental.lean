/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM19/SchrodingerFundamental.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM16.FourierInversion
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM16.FourierInversion
open Complex Finset MeasureTheory


noncomputable section

/-- Squared Euclidean norm $|x|^2 = \sum_{i=1}^n (x^i)^2$ for $x \in \mathbb{R}^n$. -/
def euclidNormSq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, (x i) ^ 2

/-- The Schrödinger fundamental solution (Definition 2.0.1) in $n$ spatial dimensions:
$$K(t, x) = \frac{1}{(2\pi i t)^{n/2}}\, \exp\!\left(\frac{i|x|^2}{2t}\right).$$ -/
def schrodingerKernel (n : ℕ) (t : ℝ) (x : Fin n → ℝ) : ℂ :=
  (2 * ↑Real.pi * I * ↑t) ^ (-(↑n : ℂ) / 2) *
  exp (I * ↑(euclidNormSq x) / (2 * ↑t))

/-- The partial derivative $\partial_j f(x)$ of a function $f : \mathbb{R}^n \to \mathbb{C}$
in the $j$-th coordinate direction, defined as the one-variable derivative obtained by varying
the $j$-th coordinate while keeping the others fixed. -/
def spatialPartialDeriv {n : ℕ} (j : Fin n) (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  deriv (fun s => f (Function.update x j s)) (x j)

/-- The spatial Laplacian $\Delta f = \sum_{j=1}^n \partial_j^2 f$. -/
def spatialLaplacian {n : ℕ} (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  ∑ j, spatialPartialDeriv j (spatialPartialDeriv j f) x

/-- The free Schrödinger operator $i\,\partial_t u + \tfrac{1}{2}\Delta u$ applied to a
time-dependent field $u(t, x)$. -/
def schrodingerOp (n : ℕ) (u : ℝ → (Fin n → ℝ) → ℂ) (t : ℝ) (x : Fin n → ℝ) : ℂ :=
  I * deriv (fun s => u s x) t + (1 / 2) * spatialLaplacian (u t) x

/-- Dot product $\xi \cdot x = \sum_{i=1}^n \xi_i x_i$ on $\mathbb{R}^n$ indexed by $\text{Fin } n$. -/
def finDotProduct {n : ℕ} (ξ x : Fin n → ℝ) : ℝ := ∑ i, ξ i * x i

/-- Fourier transform on $\mathbb{R}^n$ with the analyst convention used in the book:
$\hat f(\xi) = \int_{\mathbb{R}^n} f(x)\, e^{-2\pi i \xi \cdot x}\, d^n x.$ -/
def fourierTransformFin {n : ℕ} (f : (Fin n → ℝ) → ℂ) (ξ : Fin n → ℝ) : ℂ :=
  ∫ x : Fin n → ℝ, f x * exp ((↑(-2 * Real.pi * finDotProduct ξ x) : ℂ) * I)

/-- Inverse Fourier transform on $\mathbb{R}^n$:
$f^\vee(x) = \int_{\mathbb{R}^n} f(\xi)\, e^{2\pi i \xi \cdot x}\, d^n \xi.$ -/
def inverseFourierTransformFin {n : ℕ} (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  ∫ ξ : Fin n → ℝ, f ξ * exp ((↑(2 * Real.pi * finDotProduct ξ x) : ℂ) * I)

/-- The spatial Fourier transform of the Schrödinger kernel:
$\hat K(t, \xi) = e^{-2\pi^2 i t |\xi|^2}.$ -/
def schrodingerKernelFT (n : ℕ) (t : ℝ) (ξ : Fin n → ℝ) : ℂ :=
  exp (((-2 * ↑(Real.pi ^ 2) * ↑t * ↑(euclidNormSq ξ)) : ℂ) * I)

/-- The spatial Fourier transform of the (candidate) solution $\psi(t, \cdot)$:
$\hat\psi(t, \xi) = \hat K(t, \xi)\,\hat\phi(\xi).$ -/
def schrodingerSolutionFT (n : ℕ) (φ : (Fin n → ℝ) → ℂ) (t : ℝ) (ξ : Fin n → ℝ) : ℂ :=
  schrodingerKernelFT n t ξ * fourierTransformFin φ ξ

/-- The convolution representation of the Schrödinger solution:
$\psi(t, x) = (K(t, \cdot) * \phi)(x) = \int K(t, x - y)\,\phi(y)\, d^n y.$ -/
def schrodingerConvolution (n : ℕ) (φ : (Fin n → ℝ) → ℂ) (t : ℝ) (x : Fin n → ℝ) : ℂ :=
  ∫ y : Fin n → ℝ, schrodingerKernel n t (x - y) * φ y

/-- The regularized Gaussian replacing the oscillatory kernel: for $\delta > 0$,
$g_\delta(t, \xi) = \exp\!\left(-2\pi^2 (\delta + i) t |\xi|^2\right).$
As $\delta \downarrow 0$, $g_\delta \to \hat K(t, \cdot)$ and the Gaussian is integrable, which
permits a rigorous Fourier-inversion argument. -/
def regularizedGaussian (n : ℕ) (δ : ℝ) (t : ℝ) (ξ : Fin n → ℝ) : ℂ :=
  exp ((-2 * ↑(Real.pi ^ 2) * (↑δ + I) * ↑t * ↑(euclidNormSq ξ) : ℂ))

/-- The closed-form inverse Fourier transform of the regularized Gaussian:
$$g_\delta^\vee(t, z) = (2\pi(\delta + i)t)^{-n/2}\, \exp\!\left(\frac{-|z|^2}{2t(\delta + i)}
\right).$$
At $\delta = 0$ this formally recovers the Schrödinger kernel $K(t, z)$. -/
def regularizedGaussianInverseFT (n : ℕ) (δ : ℝ) (t : ℝ) (z : Fin n → ℝ) : ℂ :=
  (2 * ↑Real.pi * (↑δ + I) * ↑t) ^ (-(↑n : ℂ) / 2) *
  exp (-(↑(euclidNormSq z) : ℂ) / (2 * ↑t * (↑δ + I)))

/-- The complex-scaled Gaussian $x \mapsto \exp(-\pi z |x|^2)$ for $z \in \mathbb{C}$ with
$\operatorname{Re} z > 0$. -/
def scaledGaussian (n : ℕ) (z : ℂ) (x : Fin n → ℝ) : ℂ :=
  exp (-(↑Real.pi * z * ↑(CM16.euclidNormSq x)))

end
