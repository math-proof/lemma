/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM16.FourierTransform
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM16.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.FourierMultiplier
import Abbrev.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM17.Schrodinger
open MeasureTheory Complex FourierTransform


noncomputable section

namespace SchrodingerEquation

/-- The predicate that $\psi : \mathbb{R} \times \mathbb{R} \to \mathbb{C}$ solves the 1D free
Schrödinger equation $i\partial_t \psi + \tfrac{1}{2}\partial_x^2 \psi = 0$ on $t > 0$. -/
def IsFreeSchrodingerSolution (ψ : ℝ → ℝ → ℂ) : Prop :=
  ∀ t > (0 : ℝ), ∀ x : ℝ,
    I * deriv (fun s => ψ s x) t +
    (1 / 2 : ℂ) * deriv (deriv (ψ t)) x = 0

/-- The complex Laplacian $\Delta f(x) = \sum_{j=1}^n \partial_{x_j}^2 f(x)$ for a complex-valued
function $f : \mathbb{R}^n \to \mathbb{C}$, defined via iterated Fréchet derivatives along the
standard basis directions. -/
def complexLaplacian {n : ℕ} (f : Rn n → ℂ) (x : Rn n) : ℂ :=
  ∑ j : Fin n, fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x (EuclideanSpace.single j 1)

/-- The predicate that $\psi : \mathbb{R} \times \mathbb{R}^n \to \mathbb{C}$ solves the
$n$-dimensional free Schrödinger equation $i\partial_t \psi + \tfrac{1}{2}\Delta \psi = 0$
on $t > 0$. -/
def IsFreeSchrodingerSolutionND {n : ℕ} (ψ : ℝ → Rn n → ℂ) : Prop :=
  ∀ t > (0 : ℝ), ∀ x : Rn n,
    I * deriv (fun s => ψ s x) t +
    (1 / 2 : ℂ) * complexLaplacian (ψ t) x = 0

/-- The Fourier transform of the 1D Schrödinger fundamental solution:
$\hat{K}(t, \xi) = e^{-2\pi^2 i t \xi^2}$. -/
def fundamentalSolutionFT (t ξ : ℝ) : ℂ :=
  exp (((-2 * Real.pi ^ 2 * t * ξ ^ 2 : ℝ) : ℂ) * I)

/-- The Fourier transform of the 1D free Schrödinger solution with initial data $\phi$:
$\hat{\psi}(t,\xi) = \hat{K}(t,\xi)\hat{\phi}(\xi)$. -/
def solutionFT (φ : ℝ → ℂ) (t ξ : ℝ) : ℂ :=
  fundamentalSolutionFT t ξ * CM16.fourierTransform φ ξ

/-- **Definition 2.0.1.** The fundamental solution to the free Schrödinger equation in
$\mathbb{R}^n$:
$$K(t, x) = \frac{1}{(2\pi i t)^{n/2}} e^{i |x|^2 / (2t)}.$$ -/
def schrodingerKernel {n : ℕ} (t : ℝ) (x : Rn n) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ) * I * (t : ℂ)) ^ (-(↑n : ℂ) / 2) *
  exp (I * ((‖x‖ ^ 2 / (2 * t) : ℝ) : ℂ))

/-- The 1D specialization of the Schrödinger fundamental solution:
$K(t, x) = (2\pi i t)^{-1/2} e^{i x^2 / (2t)}$ for $x \in \mathbb{R}$. -/
def schrodingerKernel1D (t x : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ) * I * (t : ℂ)) ^ (-(1 : ℂ) / 2) *
  exp (I * ((x ^ 2 / (2 * t) : ℝ) : ℂ))

/-- The convolution $(K(t, \cdot) * \phi)(x) = \int_{\mathbb{R}} K(t, x - y) \phi(y) \, dy$
in 1D, giving the candidate solution to the free Schrödinger equation with initial data $\phi$. -/
def schrodingerConvolution (φ : ℝ → ℂ) (t x : ℝ) : ℂ :=
  ∫ y : ℝ, schrodingerKernel1D t (x - y) * φ y

/-- The second partial derivative of the $n$-dimensional Schrödinger kernel in the $j$-th direction:
$\partial_{x_j}^2 K(t,x) = K(t,x) \cdot \left(\frac{i}{t} + \left(\frac{i x_j}{t}\right)^2\right)$. -/
def schrodingerSolution (φ : ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun t x => schrodingerConvolution φ t x

/-- The convolution $(K(t,\cdot) * \phi)(x) = \int_{\mathbb{R}^n} K(t, x - y) \phi(y) \, d^n y$
in $n$ dimensions. -/
def schrodingerConvolutionND {n : ℕ} (φ : Rn n → ℂ) (t : ℝ) (x : Rn n) : ℂ :=
  ∫ y : Rn n, schrodingerKernel t (x - y) * φ y

/-- The candidate $n$-dimensional solution $\psi(t, x) = (K(t, \cdot) * \phi)(x)$ to the free
Schrödinger equation with initial data $\phi : \mathbb{R}^n \to \mathbb{C}$. -/
def schrodingerSolutionND {n : ℕ} (φ : Rn n → ℂ) : ℝ → Rn n → ℂ :=
  fun t x => schrodingerConvolutionND φ t x

/-- The Fourier transform of the 1D Schrödinger convolution equals the multiplier representation:
$\widehat{K(t, \cdot) * \phi}(\xi) = \hat{K}(t, \xi) \hat{\phi}(\xi)$. -/
def fourierTransformRn {n : ℕ} (f : Rn n → ℂ) (ξ : Rn n) : ℂ :=
  ∫ x : Rn n, f x * Complex.exp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ x) * I)

/-- The Fourier transform of the $n$D Schrödinger fundamental solution:
$\hat{K}(t, \xi) = e^{-2\pi^2 i t |\xi|^2}$. -/
def fundamentalSolutionFT_nD {n : ℕ} (t : ℝ) (ξ : Rn n) : ℂ :=
  exp (((-2 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2 : ℝ) : ℂ) * I)

/-- The Fourier transform of the $n$D free Schrödinger solution with initial data $\phi$:
$\hat{\psi}(t, \xi) = \hat{K}(t, \xi) \hat{\phi}(\xi)$. -/
def solutionFT_nD {n : ℕ} (φ : Rn n → ℂ) (t : ℝ) (ξ : Rn n) : ℂ :=
  fundamentalSolutionFT_nD t ξ * fourierTransformRn φ ξ

end SchrodingerEquation
end
