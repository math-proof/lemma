/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM1/NormsDivergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open scoped ENNReal
open MeasureTheory Finset BigOperators

noncomputable section

namespace VectorCalculus

/-- The $C^k$ norm on $\Omega \subset \mathbb{R}$ (Definition 7.1.1):
$\|f\|_{C^k(\Omega)} = \sum_{a=0}^{k} \sup_{x \in \Omega} |f^{(a)}(x)|$. -/
def ckNorm (k : ℕ) (Ω : Set ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ a ∈ range (k + 1), ⨆ x ∈ Ω, ‖iteratedDeriv a f x‖

/-- The $L^p$ norm of $f$ on $\Omega \subset \mathbb{R}^n$ (Definition 7.1.2):
$\|f\|_{L^p(\Omega)} = \left(\int_\Omega |f(x)|^p\, d^n x\right)^{1/p}$. -/
def lpNorm {n : ℕ} (p : ℝ) (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (μ : Measure (Fin n → ℝ) := by volume_tac) : ℝ :=
  (∫ x in Ω, ‖f x‖ ^ p ∂μ) ^ (1 / p)

/-- A vector field on $\mathbb{R}^n$ (Definition 7.2.1):
an $\mathbb{R}^n$-valued function $\mathbf{F} : \mathbb{R}^n \to \mathbb{R}^n$. -/
def VectorField (n : ℕ) := (Fin n → ℝ) → (Fin n → ℝ)

/-- The divergence of a vector field $\mathbf{F}$ on $\mathbb{R}^n$ (Definition 7.2.2):
$\nabla \cdot \mathbf{F}(x) = \sum_{i=1}^n \partial_i F^i(x)$. -/
def divergence {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, fderiv ℝ (fun y => F y i) x (Pi.single i 1)

/-- The (opaque) outward unit normal vector $\hat{\mathbf{N}}(\sigma)$ to the boundary
$\partial \Omega$ at a point $\sigma$, used in the statement of the divergence theorem. -/
opaque outwardUnitNormal {n : ℕ} (Ω : Set (Fin n → ℝ)) (σ : Fin n → ℝ) : Fin n → ℝ

/-- The (opaque) surface measure $d\sigma$ on the boundary of $\Omega$, used in
the statement of the divergence theorem. -/
opaque surfaceMeasure {n : ℕ} (Ω : Set (Fin n → ℝ)) : Measure (Fin n → ℝ)

/-- The boundary flux integral
$\int_{\partial \Omega} \mathbf{F}(\sigma) \cdot \hat{\mathbf{N}}(\sigma)\, d\sigma$
appearing on the right-hand side of the divergence theorem. -/
noncomputable def boundaryFluxIntegral {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (F : (Fin n → ℝ) → (Fin n → ℝ)) : ℝ :=
  ∫ σ in frontier Ω, (∑ i : Fin n, F σ i * outwardUnitNormal Ω σ i) ∂(surfaceMeasure Ω)

/-- Divergence theorem (Theorem 7.1): for a sufficiently regular domain $\Omega$
and a $C^1$ vector field $\mathbf{F}$,
$\int_\Omega \nabla \cdot \mathbf{F}\, d^n x =
\int_{\partial \Omega} \mathbf{F}(\sigma) \cdot \hat{\mathbf{N}}(\sigma)\, d\sigma$. -/
end VectorCalculus
