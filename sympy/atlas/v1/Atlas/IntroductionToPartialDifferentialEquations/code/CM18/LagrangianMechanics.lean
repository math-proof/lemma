/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM18/LagrangianMechanics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Real Set MeasureTheory

noncomputable section

namespace CM18

/-- Spacetime $\mathbb{R}^{1+n}$ modeled as functions $\text{Fin}(n+1) \to \mathbb{R}$.
The component indexed by $0$ is time and components $1, \ldots, n$ are spatial. -/
abbrev Spacetime (n : ℕ) := Fin (n + 1) → ℝ

/-- A real-valued scalar field on $(1+n)$-dimensional spacetime. -/
abbrev ScalarField (n : ℕ) := Spacetime n → ℝ

/-- A Lagrangian (Definition 1.0.1) is a function of the field value $\phi \in \mathbb{R}$,
its spacetime gradient $\nabla\phi \in \mathbb{R}^{1+n}$, and the spacetime coordinate $x$.
We write $\mathcal{L}(\phi, \nabla\phi, x)$. -/
def Lagrangian (n : ℕ) := ℝ → (Fin (n + 1) → ℝ) → Spacetime n → ℝ

/-- The spacetime gradient $\nabla\phi$ of a scalar field $\phi$ at $x$, given by the components
$(\nabla\phi)_\mu = \partial_\mu \phi(x) = (D\phi)_x(e_\mu)$ where $e_\mu$ is the $\mu$-th
coordinate vector. -/
def spacetimeGradient {n : ℕ} (φ : ScalarField n) (x : Spacetime n) : Fin (n + 1) → ℝ :=
  fun μ => fderiv ℝ φ x (Pi.single μ 1)

/-- The action (Definition 1.0.2) of a field $\phi$ over a compact set $\mathfrak{K} \subset
\mathbb{R}^{1+n}$:
$$\mathcal{A}[\phi; \mathfrak{K}] = \int_{\mathfrak{K}} \mathcal{L}(\phi(x), \nabla\phi(x), x)\,
d^{1+n}x.$$ -/
def action {n : ℕ} (L : Lagrangian n) (φ : ScalarField n) (K : Set (Spacetime n)) : ℝ :=
  ∫ x in K, L (φ x) (spacetimeGradient φ x) x

/-- A variation (Definition 1.0.3) on a set $K$ is a smooth scalar field $\psi$ whose support
is contained in $K$; equivalently $\psi \in C_c^\infty(K)$. -/
def IsVariation {n : ℕ} (K : Set (Spacetime n)) (ψ : ScalarField n) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ψ ∧ Function.support ψ ⊆ K

/-- The perturbed field (Definition 1.0.4) $\phi_\varepsilon := \phi + \varepsilon\psi$. -/
def perturbedField {n : ℕ} (φ ψ : ScalarField n) (ε : ℝ) : ScalarField n :=
  fun x => φ x + ε * ψ x

/-- $\phi$ is a stationary point of the action (Definition 1.0.5) iff for every compact set
$\mathfrak{K}$ and every variation $\psi \in C_c^\infty(\mathfrak{K})$,
$$\left.\frac{d}{d\varepsilon}\right|_{\varepsilon=0} \mathcal{A}[\phi_\varepsilon;
\mathfrak{K}] = 0.$$ -/
def IsStationaryPoint {n : ℕ} (L : Lagrangian n) (φ : ScalarField n) : Prop :=
  ∀ (K : Set (Spacetime n)) (_hK : IsCompact K) (ψ : ScalarField n),
    IsVariation K ψ →
      deriv (fun ε => action L (perturbedField φ ψ ε) K) 0 = 0

/-- The partial derivative $\partial\mathcal{L}/\partial\phi$ evaluated at $(\phi(x),
\nabla\phi(x), x)$. -/
def dL_dφ {n : ℕ} (L : Lagrangian n) (φ : ScalarField n) (x : Spacetime n) : ℝ :=
  deriv (fun v => L v (spacetimeGradient φ x) x) (φ x)

/-- The partial derivative $\partial\mathcal{L}/\partial(\nabla_\alpha\phi)$ evaluated at
$(\phi(x), \nabla\phi(x), x)$, holding the other gradient components, $\phi$, and $x$ fixed. -/
def dL_dgrad {n : ℕ} (L : Lagrangian n) (φ : ScalarField n)
    (x : Spacetime n) (α : Fin (n + 1)) : ℝ :=
  fderiv ℝ (fun p => L (φ x) p x) (spacetimeGradient φ x) (Pi.single α 1)

/-- The Euler-Lagrange operator
$$E[\phi](x) = \frac{\partial\mathcal{L}}{\partial\phi} - \sum_\alpha \nabla_\alpha\left(
\frac{\partial\mathcal{L}}{\partial(\nabla_\alpha\phi)}\right).$$
The Euler-Lagrange PDE (Theorem 1.1) is $E[\phi] = 0$. -/
def eulerLagrangeOperator {n : ℕ} (L : Lagrangian n) (φ : ScalarField n)
    (x : Spacetime n) : ℝ :=
  dL_dφ L φ x - ∑ α : Fin (n + 1),
    fderiv ℝ (fun y => dL_dgrad L φ y α) x (Pi.single α 1)
