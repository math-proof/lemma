/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/FlowSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM17.FlowSymmetry
open Real Set MeasureTheory


noncomputable section

namespace ODEFlow

/-- Transformation of a scalar field under a change of coordinates:
$\widetilde{\varphi}(\widetilde{x}) = \varphi(F^{-1}(\widetilde{x}))$
(cf. Definition 2.0.6). -/
def transformScalar {n : ℕ} (φ : ScalarField n)
    (Finv : Spacetime n → Spacetime n) : ScalarField n :=
  fun xt => φ (Finv xt)

/-- Transformation of the spacetime gradient of a scalar field under a change of
coordinates (Definition 2.0.6):
$\widetilde{\nabla}_\mu \widetilde{\varphi} = (M^{-1})_\mu{}^\alpha \nabla_\alpha \varphi$,
expressed using the Jacobian of $F^{-1}$. -/
def transformGradient {n : ℕ} (φ : ScalarField n)
    (Finv : Spacetime n → Spacetime n) (xt : Spacetime n) :
    Fin (n + 1) → ℝ :=
  fun μ => ∑ α : Fin (n + 1),
    jacobian Finv xt α μ * spacetimeGradient φ (Finv xt) α

/-- Transformation of a metric under a change of coordinates (Definition 2.0.6):
$\widetilde{m}_{\mu\nu} = (M^{-1})_\mu{}^\alpha (M^{-1})_\nu{}^\beta m_{\alpha\beta}$,
expressed using the Jacobian of $F^{-1}$. -/
def transformMetric {n : ℕ} (m : Metric n)
    (Finv : Spacetime n → Spacetime n) : Metric n :=
  fun xt μ ν => ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
    jacobian Finv xt α μ * jacobian Finv xt β ν * m (Finv xt) α β

/-- A Lagrangian as a function of $(\varphi, \nabla \varphi, m)$:
the scalar field value, its gradient, and the metric components. -/
def MetricLagrangian (n : ℕ) :=
  ℝ → (Fin (n + 1) → ℝ) → (Fin (n + 1) → Fin (n + 1) → ℝ) → ℝ

/-- A Lagrangian $\mathcal{L}(\varphi, \nabla \varphi, m)$ is coordinate invariant
(Definition 2.0.7) if for every smooth diffeomorphism $\Psi$ and every scalar field
$\varphi$ and metric $m$, the value $\mathcal{L}$ evaluated on the original fields at
$x$ equals $\mathcal{L}$ evaluated on the transformed fields at $\widetilde{x} = \Psi(x)$. -/
def IsCoordinateInvariant {n : ℕ} (L : MetricLagrangian n) : Prop :=
  ∀ (Fmap Finv : Spacetime n → Spacetime n),
    (∀ x, Finv (Fmap x) = x) →
    (∀ xt, Fmap (Finv xt) = xt) →
    ContDiff ℝ ⊤ Fmap →
    ContDiff ℝ ⊤ Finv →
    ∀ (φ : ScalarField n) (m : Metric n) (x : Spacetime n),
      let xt := Fmap x
      L (φ x) (spacetimeGradient φ x) (m x) =
      L (transformScalar φ Finv xt)
        (transformGradient φ Finv xt)
        (transformMetric m Finv xt)

end ODEFlow
end
