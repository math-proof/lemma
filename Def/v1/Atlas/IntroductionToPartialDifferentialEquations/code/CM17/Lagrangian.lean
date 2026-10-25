/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Lagrangian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM17.Lagrangian
open Real Set MeasureTheory


noncomputable section

namespace CM17Lagrangian

/-- A Lagrangian density $L(\phi, \partial \phi, x)$: a real-valued function of the field
value, the spacetime gradient (an $(n+1)$-tuple of partial derivatives), and the spacetime
point. -/
def Lagrangian (n : ℕ) := ℝ → (Fin (n + 1) → ℝ) → Spacetime n → ℝ

/-- The spacetime gradient $(\partial_{\mu} \phi)_{\mu = 0, \ldots, n}$ of a scalar field
$\phi$ at the point $x$, i.e. the $(n+1)$-tuple of partial derivatives. -/
def spacetimeGradient {n : ℕ} (φ : ScalarField n) (x : Spacetime n) : Fin (n + 1) → ℝ :=
  fun μ => fderiv ℝ φ x (Pi.single μ 1)

/-- The action functional $\mathcal{S}_K[\phi] = \int_K L(\phi(x), \partial \phi(x), x)\, dx$
of a scalar field $\phi$ on a region $K \subset \mathbb{R}^{1+n}$. -/
def action {n : ℕ} (L : Lagrangian n) (φ : ScalarField n) (K : Set (Spacetime n)) : ℝ :=
  ∫ x in K, L (φ x) (spacetimeGradient φ x) x

/-- A variation $\psi$ supported in $K$: a smooth ($C^{\infty}$) scalar field whose support
is contained in the region $K$. This is the class of admissible test perturbations of
$\phi$. -/
def IsVariation {n : ℕ} (K : Set (Spacetime n)) (ψ : ScalarField n) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ψ ∧ Function.support ψ ⊆ K

/-- The one-parameter perturbation $\phi_{\varepsilon}(x) = \phi(x) + \varepsilon \psi(x)$
used to define the first variation of the action. -/
def perturbedField {n : ℕ} (φ ψ : ScalarField n) (ε : ℝ) : ScalarField n :=
  fun x => φ x + ε * ψ x

/-- A scalar field $\phi$ is a stationary point of the action: for every compact region $K$
and every variation $\psi$ supported in $K$, the first variation of the action vanishes,
$\left. \frac{d}{d\varepsilon} \right|_{\varepsilon = 0}
\mathcal{S}_K[\phi + \varepsilon \psi] = 0$. -/
def IsStationaryPoint {n : ℕ} (L : Lagrangian n) (φ : ScalarField n) : Prop :=
  ∀ (K : Set (Spacetime n)) (_hK : IsCompact K) (ψ : ScalarField n),
    IsVariation K ψ →
      deriv (fun ε => action L (perturbedField φ ψ ε) K) 0 = 0

/-- Partial derivative of the Lagrangian with respect to the field value $\phi$:
$\partial L / \partial \phi$ evaluated at $(\phi(x), \partial \phi(x), x)$. -/
def dL_dφ {n : ℕ} (L : Lagrangian n) (φ : ScalarField n) (x : Spacetime n) : ℝ :=
  deriv (fun v => L v (spacetimeGradient φ x) x) (φ x)

/-- Partial derivative of the Lagrangian with respect to the $\alpha$-th component of the
gradient: $\partial L / \partial(\partial_{\alpha} \phi)$ evaluated at
$(\phi(x), \partial \phi(x), x)$. -/
def dL_dgrad {n : ℕ} (L : Lagrangian n) (φ : ScalarField n)
    (x : Spacetime n) (α : Fin (n + 1)) : ℝ :=
  fderiv ℝ (fun p => L (φ x) p x) (spacetimeGradient φ x) (Pi.single α 1)

/-- The Euler-Lagrange operator applied to $\phi$ at $x$:
$\mathrm{EL}[\phi](x) = \dfrac{\partial L}{\partial \phi}
- \sum_{\alpha} \partial_{\alpha} \!\left( \dfrac{\partial L}{\partial(\partial_{\alpha} \phi)} \right)$.
A scalar field is stationary iff this operator vanishes identically. -/
def eulerLagrangeOperator {n : ℕ} (L : Lagrangian n) (φ : ScalarField n)
    (x : Spacetime n) : ℝ :=
  dL_dφ L φ x - ∑ α : Fin (n + 1),
    fderiv ℝ (fun y => dL_dgrad L φ y α) x (Pi.single α 1)

end CM17Lagrangian
end
