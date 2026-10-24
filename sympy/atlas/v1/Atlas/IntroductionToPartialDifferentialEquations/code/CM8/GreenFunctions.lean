/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Real Set Topology

noncomputable section

namespace CM8

/-- Opaque predicate: $\Omega \subset \mathbb{R}^n$ is a (bounded) Lipschitz
domain. Left abstract here since regularity details of the boundary are not
used in these formal statements. -/
opaque IsLipschitzDomain : {n : ℕ} → Set (Fin n → ℝ) → Prop

/-- The Euclidean norm on $\mathbb{R}^n$ written as
$\|x\| = \sqrt{\sum_i x_i^2}$. -/
def euclidNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- The fundamental solution of the Laplacian in $\mathbb{R}^3$:
$\Phi(x) = -\dfrac{1}{4 \pi |x|}$, away from the origin. -/
def Phi3 (x : Fin 3 → ℝ) : ℝ :=
  -1 / (4 * Real.pi * euclidNorm x)

/-- The Laplacian of $f : \mathbb{R}^n \to \mathbb{R}$ at $x$, defined in terms
of Fréchet derivatives applied to coordinate unit vectors:
$\Delta f(x) = \sum_{i = 1}^{n} \partial_i (\partial_i f)(x)$. -/
noncomputable def laplacian {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n,
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single i 1)


section HarmonicProofHelpers

open Finset

/-- The squared Euclidean norm $\|y\|^2 = \sum_j y_j^2$ on $\mathbb{R}^3$. -/
private def normSq (y : Fin 3 → ℝ) : ℝ := ∑ j : Fin 3, y j ^ 2

/-- The continuous linear map representing the Fréchet derivative of
$y \mapsto \sum_j y_j^2$ at $x$: it acts as $v \mapsto 2 \sum_j x_j v_j$. -/
def normSq_CLM (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ∑ j : Fin 3, (2 * x j) • ContinuousLinearMap.proj (R := ℝ) (ι := Fin 3) (φ := fun _ => ℝ) j


/-- The sum of squares of the coordinates of $x$ other than the $i$-th:
$\sum_{j \ne i} x_j^2$. Used to reduce a multivariable derivative to a
one-dimensional computation. -/
def restSq (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  ∑ j ∈ Finset.univ.filter (· ≠ i), x j ^ 2

/-- **Definition 2.0.2 (Green function for a domain).** Data of a Green
function for a domain $\Omega \subset \mathbb{R}^3$: a `corrector`
$\phi(x, y)$ which matches the fundamental solution on the boundary, i.e.
$\phi(x, \sigma) = \Phi_3(x - \sigma)$ for $x \in \Omega$ and $\sigma \in
\partial \Omega$. -/
structure GreenFunction (Ω : Set (Fin 3 → ℝ)) where
  corrector : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ
  corrector_boundary : ∀ x ∈ Ω, ∀ σ ∈ frontier Ω,
    corrector x σ = Phi3 (x - σ)

/-- The Green function $G(x, y) = \Phi_3(x - y) - \phi(x, y)$ assembled from a
fundamental solution and its corrector. -/
def GreenFunction.G {Ω : Set (Fin 3 → ℝ)} (gf : GreenFunction Ω)
    (x y : Fin 3 → ℝ) : ℝ :=
  Phi3 (x - y) - gf.corrector x y

/-- Abstract placeholder for the outward normal derivative
$\nabla_{\hat{N}(\sigma)} f$ of a function $f$ at a boundary point $\sigma$ of
$\Omega$. -/
opaque normalDerivGF (Ω : Set (Fin 3 → ℝ)) (f : (Fin 3 → ℝ) → ℝ)
    (σ : Fin 3 → ℝ) : ℝ

/-- Abstract placeholder for the boundary surface integral
$\int_{\partial \Omega} f(\sigma) \, d\sigma$. -/
opaque surfaceIntegralGF (Ω : Set (Fin 3 → ℝ)) (f : (Fin 3 → ℝ) → ℝ) : ℝ

/-- Abstract placeholder for the integral of $f$ over the sphere of radius
$\varepsilon$ centred at $x$: $\int_{\partial B_\varepsilon(x)} f \, d\sigma$. -/
opaque sphereIntegralGF (x : Fin 3 → ℝ) (ε : ℝ) (f : (Fin 3 → ℝ) → ℝ) : ℝ


/-- Green's identity on the punctured domain $\Omega \setminus B_\varepsilon(x)$:
the volume integral of $\Phi_3(x - y) \Delta u(y)$ equals a difference of
boundary surface integrals minus a sphere integral around the singularity. -/
structure IsGreenDecomposition {n : ℕ} (Ω : Set (Fin n → ℝ))
    (Φ : (Fin n → ℝ) → ℝ)
    (G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (φ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : Prop where
  decomposition : ∀ x y : Fin n → ℝ, G x y = Φ (x - y) - φ x y
  corrector_harmonic : ∀ x ∈ Ω, ∀ y ∈ Ω, laplacian (φ x) y = 0
  corrector_boundary : ∀ x ∈ Ω, ∀ σ ∈ frontier Ω, φ x σ = Φ (x - σ)
