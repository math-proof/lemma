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
import sympy.atlas.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM9.PoissonHarnackLiouville
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM9.PoissonHarnackLiouville

open Real Set MeasureTheory Filter

noncomputable section

namespace LaplacePoisson

/-- A bounded Lipschitz domain in $\mathbb{R}^n$: an open, bounded, nonempty,
connected set whose boundary can be locally straightened by bi-Lipschitz maps.
This is the natural class of domains for the Poisson Dirichlet problem. -/
structure IsLipschitzDomain {n : ℕ} (Ω : Set (Fin n → ℝ)) : Prop where
  isOpen : IsOpen Ω
  isBounded : Bornology.IsBounded Ω
  nonempty : Set.Nonempty Ω
  isConnected : IsConnected Ω
  frontier_nonempty : Set.Nonempty (frontier Ω)
  lipschitz_boundary : ∀ x ∈ frontier Ω, ∃ (U : Set (Fin n → ℝ)),
    IsOpen U ∧ x ∈ U ∧
    ∃ (φ : (Fin n → ℝ) → (Fin n → ℝ)),
      LipschitzWith 1 φ ∧
      ∃ (ψ : (Fin n → ℝ) → (Fin n → ℝ)),
        LipschitzWith 1 ψ ∧
        (∀ y ∈ U, ψ (φ y) = y) ∧ (∀ z ∈ φ '' U, φ (ψ z) = z)

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

/-- Bundled Green's function for the Dirichlet Laplacian on a domain $\Omega$:
$G(x, \cdot)$ vanishes on $\partial\Omega$, satisfies the distributional identity
$\Delta_y G(x, y) = -\delta_x$ (here stated against test functions), and comes with
the integrability data needed for Green's representation formula. -/
structure GreenFunctionLP (n : ℕ) (Ω : Set (Fin n → ℝ)) where
  G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  domain_open : IsOpen Ω
  boundary_zero : ∀ x ∈ Ω, ∀ σ ∈ frontier Ω, G x σ = 0
  distributional_pde : ∀ x ∈ Ω, ∀ φ : (Fin n → ℝ) → ℝ,
    ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    ∫ y, G x y * laplacianLP φ y = φ x
  G_differentiable : ∀ x ∈ Ω, ∀ σ, DifferentiableAt ℝ (G x) σ
  Phi_differentiable : ∀ x : Fin n → ℝ, ∀ σ,
    DifferentiableAt ℝ (fun y => fundamentalSolution n (x - y)) σ
  G_mul_integrableOn : ∀ x ∈ Ω, ∀ f : (Fin n → ℝ) → ℝ,
    Bornology.IsBounded Ω →
    IntegrableOn (fun y => G x y * f y) Ω
  Phi_mul_integrableOn : ∀ x : Fin n → ℝ, ∀ f : (Fin n → ℝ) → ℝ,
    Bornology.IsBounded Ω →
    IntegrableOn (fun y => fundamentalSolution n (x - y) * f y) Ω
  G_normalDeriv_integrableOn : ∀ x ∈ Ω, ∀ g : (Fin n → ℝ) → ℝ,
    IntegrableOn (fun σ => g σ * normalDerivLP Ω (G x) σ)
      (frontier Ω) (surfaceMeasure Ω)
  Phi_normalDeriv_integrableOn : ∀ x : Fin n → ℝ, ∀ g : (Fin n → ℝ) → ℝ,
    IntegrableOn (fun σ => g σ * normalDerivLP Ω (fun y => fundamentalSolution n (x - y)) σ)
      (frontier Ω) (surfaceMeasure Ω)

/-- **Weyl's lemma**: a function whose integral against $\Delta\psi$ vanishes for
every test function $\psi$ supported in $\Omega$ is necessarily smooth and harmonic
on $\Omega$. -/
noncomputable def sphereIntegralLP {n : ℕ} (x : Fin n → ℝ) (ε : ℝ) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ σ in frontier (Metric.ball x ε), f σ ∂(surfaceMeasure (Metric.ball x ε))

/-- Green's representation formula derived from the corrector identity: combining the
$\Phi$-version of the representation formula with the harmonic-corrector identity
$\varphi = \Phi - G$ yields the clean Green-function formula
$u(x) = \int_\Omega f \cdot G(x, \cdot) + \int_{\partial \Omega} g \cdot \partial_\nu G(x, \cdot)$. -/
def laplacianE {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n,
    fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)

/-- A function $u$ on `EuclideanSpace ℝ (Fin n)` is harmonic on $\Omega$ iff
$\Delta u = 0$ on $\Omega$. -/
def IsHarmonicE {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x ∈ Ω, laplacianE u x = 0

/-- Opaque outward unit normal on $\partial\Omega$, valued in `EuclideanSpace ℝ (Fin n)`. -/
opaque outwardUnitNormalE {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)

/-- Explicit form of the outward unit normal on a ball in $\mathbb{R}^3$:
$\nu(\sigma) = (\sigma - p)/R$ for $\sigma$ on the sphere of radius $R$ about $p$. -/
def normalDerivE {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (σ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, fderiv ℝ f σ (EuclideanSpace.single i 1) * outwardUnitNormalE Ω σ i

/-- Surface integral $\int_{\partial \Omega} f\,dS$ on `EuclideanSpace`. -/
def surfaceIntegralE {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ σ in frontier Ω, f σ ∂(surfaceMeasureE Ω)

/-- Bundled Green's function for the Dirichlet Laplacian on $\Omega \subseteq$
`EuclideanSpace ℝ (Fin n)`. Same defining properties as `GreenFunctionLP` but on the
Euclidean (rather than $L^p$) model of $\mathbb{R}^n$. -/
structure GreenFunctionE (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) where
  G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ
  domain_open : IsOpen Ω
  boundary_zero : ∀ x ∈ Ω, ∀ σ ∈ frontier Ω, G x σ = 0
  distributional_pde : ∀ x ∈ Ω, ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
    ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    ∫ y, G x y * laplacianE φ y = φ x

/-- $\Delta \Phi = \delta_x$ distributionally on `EuclideanSpace ℝ (Fin 3)`: for any
$C^2$ test function $\varphi$ with compact support,
$\int -1/(4\pi |y - x|)\,\Delta \varphi(y)\,dy = \varphi(x)$. -/
def kelvinImageE (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  p + (R / ‖x - p‖) ^ 2 • (x - p)

/-- Key Kelvin-image identity: for $\sigma$ on the sphere $\partial B(p, R)$,
$\|x^* - \sigma\| = (R/\|x - p\|)\,\|x - \sigma\|$. This produces the boundary
cancellation of $G$ on $\partial B(p, R)$. -/
def greenBallFunctionE (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ)
    (x y : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  if x = p then
    -1 / (4 * Real.pi * ‖y - p‖) + 1 / (4 * Real.pi * R)
  else
    -1 / (4 * Real.pi * ‖y - x‖) +
      (R / ‖x - p‖) * (1 / (4 * Real.pi * ‖y - kelvinImageE p R x‖))

/-- Boundary vanishing of the explicit Green's function on the ball: for every
$x \in B(p, R)$ and every $\sigma \in \partial B(p, R)$, $G(x, \sigma) = 0$.
This relies on the Kelvin-image norm identity to balance the two terms. -/
end LaplacePoisson
