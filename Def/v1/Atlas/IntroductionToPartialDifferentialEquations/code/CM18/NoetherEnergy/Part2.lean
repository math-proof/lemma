/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM18/NoetherEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM18.LagrangianMechanics
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM18.LagrangianMechanics
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM18.NoetherEnergy
open Real Set MeasureTheory


noncomputable section

namespace CM18

/-- The $(\mu,\nu)$-component of the Jacobian matrix
$M^\mu_{\ \nu} = \partial \widetilde{x}^\mu / \partial x^\nu$
of the flow map $F_\epsilon$ evaluated at $x$. -/
def FlowMap.jacobian {n : ℕ} (Psi : FlowMap n) (eps : ℝ) (x : Spacetime n)
    (mu nu : Fin (n + 1)) : ℝ :=
  fderiv ℝ (fun y => Psi.F eps y mu) x (Pi.single nu 1)

/-- The $(\mu,\nu)$-component of the inverse-Jacobian matrix
$(M^{-1})^\mu_{\ \nu} = \partial x^\mu / \partial \widetilde{x}^\nu$,
defined as the Jacobian of $F_{-\epsilon}$ at $\widetilde{x}$. -/
def FlowMap.invJacobian {n : ℕ} (Psi : FlowMap n) (eps : ℝ) (xt : Spacetime n)
    (mu nu : Fin (n + 1)) : ℝ :=
  fderiv ℝ (fun z => Psi.F (-eps) z mu) xt (Pi.single nu 1)

/-- The transformed scalar field $\widetilde{\phi}(\widetilde{x}) := \phi(F_{-\epsilon}(\widetilde{x}))$
from CM18 Definition 2.0.6. -/
def transformedField {n : ℕ} (Psi : FlowMap n) (phi : ScalarField n)
    (eps : ℝ) (xt : Spacetime n) : ℝ :=
  phi (Psi.F (-eps) xt)

/-- The transformed gradient
$\widetilde{\nabla}_\mu \widetilde{\phi}(\widetilde{x})
  := (M^{-1})^\alpha_{\ \mu} \nabla_\alpha \phi(F_{-\epsilon}(\widetilde{x}))$
from CM18 Definition 2.0.6. -/
def transformedGradient {n : ℕ} (Psi : FlowMap n) (phi : ScalarField n)
    (eps : ℝ) (xt : Spacetime n) (mu : Fin (n + 1)) : ℝ :=
  ∑ alpha : Fin (n + 1),
    Psi.invJacobian eps xt alpha mu * spacetimeGradient phi (Psi.F (-eps) xt) alpha

/-- The transformed metric components
$\widetilde{m}_{\mu\nu}(\widetilde{x})
  := (M^{-1})^\alpha_{\ \mu} (M^{-1})^\beta_{\ \nu} m_{\alpha\beta}(F_{-\epsilon}(\widetilde{x}))$
from CM18 Definition 2.0.6. -/
def transformedMetric {n : ℕ} (Psi : FlowMap n) (m : Metric n)
    (eps : ℝ) (xt : Spacetime n) (mu nu : Fin (n + 1)) : ℝ :=
  ∑ alpha : Fin (n + 1), ∑ beta : Fin (n + 1),
    Psi.invJacobian eps xt alpha mu * Psi.invJacobian eps xt beta nu *
    m (Psi.F (-eps) xt) alpha beta

/-- The transformed inverse metric components
$(\widetilde{m}^{-1})^{\mu\nu}(\widetilde{x})
  := M^\mu_{\ \alpha} M^\nu_{\ \beta} (m^{-1})^{\alpha\beta}(F_{-\epsilon}(\widetilde{x}))$
from CM18 Definition 2.0.6. -/
def transformedInverseMetric {n : ℕ} (Psi : FlowMap n) (mInv : InverseMetric n)
    (eps : ℝ) (xt : Spacetime n) (mu nu : Fin (n + 1)) : ℝ :=
  let x := Psi.F (-eps) xt
  ∑ alpha : Fin (n + 1), ∑ beta : Fin (n + 1),
    Psi.jacobian eps x mu alpha * Psi.jacobian eps x nu beta * mInv x alpha beta

/-- A metric Lagrangian $\mathcal{L}$ is **coordinate invariant** (CM18 Definition 2.0.7) if for
every smooth flow $\Psi$ on spacetime,
$\mathcal{L}(\phi(x), \nabla\phi(x), m(x))
  = \mathcal{L}(\widetilde{\phi}(\widetilde{x}),
      \widetilde{\nabla}\widetilde{\phi}(\widetilde{x}),
      \widetilde{m}(\widetilde{x}))$
where the transformed fields are as in Definition 2.0.6 and $x = F_{-\epsilon}(\widetilde{x})$. -/
def IsCoordinateInvariant {n : ℕ} (L : MetricLagrangian n) : Prop :=
  ∀ (Psi : FlowMap n) (phi : ScalarField n) (m : Metric n) (eps : ℝ)
    (xt : Spacetime n),
    let x := Psi.F (-eps) xt

    L (phi x) (spacetimeGradient phi x) (m x) =


    L (transformedField Psi phi eps xt)
      (fun mu => transformedGradient Psi phi eps xt mu)
      (fun mu nu => transformedMetric Psi m eps xt mu nu)

/-- The partial derivative $\partial \mathcal{L} / \partial m_{\mu\nu}$ of a metric Lagrangian
with respect to the $(\mu,\nu)$-entry of the metric, evaluated at $(\phi(x), \nabla\phi(x), m(x))$. -/
def dL_dm {n : ℕ} (L : MetricLagrangian n) (phi : ScalarField n)
    (m : Metric n) (x : Spacetime n)
    (mu nu : Fin (n + 1)) : ℝ :=
  fderiv ℝ (fun mval => L (phi x) (spacetimeGradient phi x) mval)
    (m x)
    (fun mu' nu' => if mu' = mu ∧ nu' = nu then 1 else 0)


set_option maxHeartbeats 800000 in

/-- The energy-momentum tensor associated to a metric Lagrangian:
$T^{\mu\nu}(x) := 2 \frac{\partial \mathcal{L}}{\partial m_{\mu\nu}}
  + (m^{-1})^{\mu\nu} \mathcal{L}(\phi, \nabla\phi, m)$.
This is the canonical "Hilbert" energy-momentum tensor obtained by varying the action with respect
to the metric. -/
def energyMomentumTensor {n : ℕ} (L : MetricLagrangian n) (phi : ScalarField n)
    (m : Metric n) (mInv : InverseMetric n) (x : Spacetime n)
    (mu nu : Fin (n + 1)) : ℝ :=
  2 * dL_dm L phi m x mu nu + mInv x mu nu * L.eval phi m x

/-- Divergence of a tensor field $T$ at a point $x$ in the $\nu$ slot:
$(\nabla \cdot T)^\nu(x) := \sum_\mu \nabla_\mu T^{\mu\nu}(x)$. -/
def tensorDivergence {n : ℕ}
    (T : Spacetime n → Fin (n + 1) → Fin (n + 1) → ℝ)
    (x : Spacetime n) (nu : Fin (n + 1)) : ℝ :=
  ∑ mu : Fin (n + 1),
    fderiv ℝ (fun y => T y mu nu) x (Pi.single mu 1)

/-- A scalar field $\phi$ satisfies the Euler-Lagrange equation for the Lagrangian $\mathcal{L}$
with metric $m$ if the Euler-Lagrange operator vanishes at every spacetime point. -/
def SatisfiesEulerLagrange {n : ℕ} (L : MetricLagrangian n)
    (phi : ScalarField n) (m : Metric n) : Prop :=
  ∀ x : Spacetime n,
    eulerLagrangeOperator (fun v p y => L v p (m y)) phi x = 0

/-- Matrix transpose viewed as an $\mathbb{R}$-linear map $\mathbb{R}^{k \times k} \to \mathbb{R}^{k \times k}$. -/
def matTransposeLM (k : ℕ) : (Fin k → Fin k → ℝ) →ₗ[ℝ] (Fin k → Fin k → ℝ) where
  toFun M := fun i j => M j i
  map_add' x y := by ext i j; simp
  map_smul' c x := by ext i j; simp

/-- Matrix transpose as a continuous $\mathbb{R}$-linear map on $\mathbb{R}^{k \times k}$. -/
def matTransposeCLM (k : ℕ) : (Fin k → Fin k → ℝ) →L[ℝ] (Fin k → Fin k → ℝ) :=
  LinearMap.toContinuousLinearMap (matTransposeLM k)

end CM18
end
