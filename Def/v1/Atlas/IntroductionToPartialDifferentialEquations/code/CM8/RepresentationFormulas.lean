/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/RepresentationFormulas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM8.GreenFunctions.Part2
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM8.GreenFunctions
open Real Set MeasureTheory


noncomputable section

namespace CM8

/-- The Newtonian-potential convolution in $\mathbb{R}^3$: given $f : \mathbb{R}^3 \to \mathbb{R}$,
`phiConvolution f x` is $\int_{\mathbb{R}^3} \Phi(x - y) f(y) \, d^3 y$, where $\Phi$ is the
3D fundamental solution of the Laplacian. -/
def phiConvolution (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∫ y : Fin 3 → ℝ, Phi3 (x - y) * f y

/-- The Laplacian $\Delta f = \sum_{i=1}^{3} \partial_i^2 f$ on $\mathbb{R}^3$, specialised from
the general `laplacian` to dimension three. -/
def laplacian3 (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  laplacian f x

/-- Leibniz/differentiation-under-the-integral for the Newtonian potential: if $f$ is smooth and
compactly supported, then $\Delta(\Phi * f)(x) = \int \Phi(x-y) \Delta f(y) \, d^3y$. -/
def normalDeriv {n : ℕ} (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (σ : Fin n → ℝ) : ℝ :=
  fderiv ℝ f σ (outwardUnitNormal Ω σ)

/-- The surface (Hausdorff) measure on $\partial\Omega$, declared opaque since its precise
construction is not used here. -/
opaque surfaceMeasure : {n : ℕ} → Set (Fin n → ℝ) → Measure (Fin n → ℝ)

/-- The surface integral $\int_{\partial\Omega} f(\sigma) \, d\sigma$ of $f$ over the boundary
of $\Omega$, with respect to the surface measure. -/
def surfaceIntegral {n : ℕ} (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ σ in frontier Ω, f σ ∂(surfaceMeasure Ω)

/-- The surface area $\omega_n$ of the unit sphere $S^{n-1} \subset \mathbb{R}^n$, given by
$\omega_n = 2 \pi^{n/2} / \Gamma(n/2)$ for $n \ge 1$. -/
def unitSphereArea (n : ℕ) : ℝ :=
  if n = 0 then 1 else 2 * Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)

/-- The fundamental solution $\Phi(x)$ of $-\Delta$ in $\mathbb{R}^n$ (equation 1.0.3): for
$n = 2$ it is $\tfrac{1}{2\pi}\log|x|$, and for $n \ge 3$ it is $-1/(\omega_n |x|^{n-2})$. -/
def FundSolN {n : ℕ} [Fact (2 ≤ n)] (x : Fin n → ℝ) : ℝ :=
  if n = 2 then
    (1 / (2 * Real.pi)) * Real.log (euclidNorm x)
  else
    -1 / (unitSphereArea n * (euclidNorm x) ^ (n - 2))

/-- Green's second identity on a Lipschitz domain $\Omega \subset \mathbb{R}^n$: for
$u, v \in C^2(\bar\Omega)$,
$$\int_\Omega \bigl(v \Delta u - u \Delta v\bigr)\, dy
   = \int_{\partial\Omega} \bigl(v \, \nabla_{\hat N} u - u \, \nabla_{\hat N} v\bigr)\, d\sigma.$$
-/
def sphereIntegral {n : ℕ} (center : Fin n → ℝ) (r : ℝ) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ σ in Metric.sphere center r, f σ ∂(surfaceMeasure (Metric.ball center r))

end CM8
end
