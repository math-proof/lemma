/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM9.PoissonHarnackLiouville
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM9.PoissonHarnackLiouville
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM7.LaplacePoisson
open Real Set MeasureTheory Filter


noncomputable section

namespace LaplacePoisson

/-- Euclidean norm on $\mathbb{R}^n$ written as $|x| = \sqrt{\sum_i (x^i)^2}$,
for vectors represented as `Fin n → ℝ` (the `LP` suffix marks the L^p-style
function space presentation). -/
def euclidNormLP {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- Surface area $\omega_n$ of the unit sphere in $\mathbb{R}^n$,
defined via the Gamma function: $\omega_n = 2\pi^{n/2}/\Gamma(n/2)$ for $n \ge 1$.
For example $\omega_3 = 4\pi$. The convention $\omega_0 = 1$ is taken here. -/
def unitSphereArea (n : ℕ) : ℝ :=
  if n = 0 then 1 else 2 * Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)

/-- The fundamental solution $\Phi$ for the Laplacian $\Delta$ in $\mathbb{R}^n$
(Definition 1.0.1 of CM7):
$\Phi(x) = \frac{1}{2\pi} \ln|x|$ for $n=2$, and
$\Phi(x) = -\frac{1}{\omega_n |x|^{n-2}}$ for $n \ge 3$,
where $\omega_n$ is the surface area of the unit sphere in $\mathbb{R}^n$. -/
def fundamentalSolution (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  if n = 2 then
    (1 / (2 * Real.pi)) * Real.log (euclidNormLP x)
  else
    -1 / (unitSphereArea n * (euclidNormLP x) ^ (n - 2))

/-- The Laplacian $\Delta f(x) = \sum_{i=1}^n \partial_i^2 f(x)$ on $\mathbb{R}^n$,
expressed in terms of `fderiv` applied twice in coordinate directions. -/
def laplacianLP {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n,
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single i 1)

/-- A function $u$ is harmonic on $\Omega$ when $\Delta u = 0$ pointwise on $\Omega$. -/
def IsHarmonicLP {n : ℕ} (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) : Prop :=
  ∀ x ∈ Ω, laplacianLP u x = 0

/-- Convolution of the fundamental solution with $f$:
$(\Phi * f)(x) = \int_{\mathbb{R}^n} \Phi(x - y)\,f(y)\,d^n y$.
This is the candidate solution of $\Delta u = f$ in Theorem 1.1 of CM7. -/
def phiConvolutionLP (n : ℕ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y : Fin n → ℝ, fundamentalSolution n (x - y) * f y

/-- Outward unit normal vector field on the boundary of $\Omega \subset \mathbb{R}^n$,
treated abstractly via an opaque declaration. -/
opaque outwardUnitNormal {n : ℕ} (Ω : Set (Fin n → ℝ)) : (Fin n → ℝ) → (Fin n → ℝ)

/-- The $(n-1)$-dimensional surface (Hausdorff) measure attached to the boundary
of $\Omega$, treated abstractly via an opaque declaration. -/
opaque surfaceMeasure {n : ℕ} (Ω : Set (Fin n → ℝ)) : Measure (Fin n → ℝ)

/-- The outward unit normal is zero off the boundary of $\Omega$. -/
def normalDerivLP {n : ℕ} (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (σ : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, fderiv ℝ f σ (Pi.single i 1) * outwardUnitNormal Ω σ i

/-- Surface integral $\int_{\partial \Omega} f \, dS$ of $f$ over the boundary
of $\Omega$ with respect to the surface measure. -/
def surfaceIntegralLP {n : ℕ} (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ σ in frontier Ω, f σ ∂(surfaceMeasure Ω)

end LaplacePoisson
end
