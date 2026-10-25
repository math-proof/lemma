/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Abbrev.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM14.WaveEnergy
open MeasureTheory Set Finset Classical


noncomputable section

namespace CM14

/-- The linear wave operator $\square_m \phi = -\partial_t^2 \phi + \sum_{i=1}^n \partial_i^2 \phi$
applied to a scalar field $\phi$ at the point $p$. -/
noncomputable def waveOp {n : ℕ} (φ : WaveScalarField n) (p : WaveSpacetime n) : ℝ :=
  -(fderiv ℝ (fun s => fderiv ℝ (fun r => φ (r, p.2)) s 1) p.1 1) +
    ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ (fun z => φ (p.1, z)) y (Pi.single i 1)) p.2 (Pi.single i 1)

/-- The partial derivative $\partial_\mu \phi(p)$ of a scalar field $\phi$ in the $\mu$-th
spacetime direction at $p$. The index $\mu = 0$ corresponds to the time derivative, and
$\mu = 1, \dots, n$ correspond to spatial derivatives. -/
noncomputable def partialDeriv {n : ℕ} (φ : WaveScalarField n) (μ : Fin (n + 1))
    (p : WaveSpacetime n) : ℝ :=
  if h : μ.val = 0 then
    fderiv ℝ (fun s => φ (s, p.2)) p.1 1
  else
    let i : Fin n := ⟨μ.val - 1, by omega⟩
    fderiv ℝ (fun y => φ (p.1, y)) p.2 (Pi.single i 1)

/-- The standard basis direction in spacetime corresponding to index $\mu$:
$e_0 = (1, 0)$ is the time direction, and $e_\mu = (0, \mathbf{e}_{\mu - 1})$ for $\mu \geq 1$. -/
def basisDir {n : ℕ} (μ : Fin (n + 1)) : ℝ × (Fin n → ℝ) :=
  if h : μ.val = 0 then (1, 0)
  else (0, Pi.single ⟨μ.val - 1, by omega⟩ 1)

/-- The Minkowski metric $m_{\mu\nu} = \operatorname{diag}(-1, 1, \dots, 1)$ on
$\mathbb{R}^{1+n}$, with mostly-plus signature. -/
def waveMinkowskiMetric (n : ℕ) (μ ν : Fin (n + 1)) : ℝ :=
  if μ = ν then (if μ.val = 0 then -1 else 1) else 0

/-- The inverse Minkowski metric $(m^{-1})^{\mu\nu}$. In the standard basis this coincides
with $m_{\mu\nu}$ since the metric is diagonal with entries $\pm 1$. -/
def minkowskiInverse (n : ℕ) (μ ν : Fin (n + 1)) : ℝ :=
  waveMinkowskiMetric n μ ν

/-- The Minkowski inner product $m(X, Y) = m_{\alpha\beta} X^\alpha Y^\beta$. -/
def minkowskiProduct {n : ℕ} (X Y : Fin (n + 1) → ℝ) : ℝ :=
  ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
    waveMinkowskiMetric n α β * X α * Y β

/-- A vector $X$ is timelike if $m(X, X) < 0$. -/
def IsTimelike {n : ℕ} (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiProduct X X < 0

/-- A vector $X$ is spacelike if $m(X, X) > 0$. -/
def IsSpacelike {n : ℕ} (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiProduct X X > 0

/-- A vector $X$ is null (lightlike) if $m(X, X) = 0$. -/
def IsNull {n : ℕ} (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiProduct X X = 0

/-- A vector $X$ is causal if it is timelike or null, i.e. $m(X, X) \leq 0$. -/
def IsCausal {n : ℕ} (X : Fin (n + 1) → ℝ) : Prop :=
  IsTimelike X ∨ IsNull X

/-- A vector $X$ is future-directed if its time component $X^0$ is positive. -/
def IsFutureDirected {n : ℕ} (X : Fin (n + 1) → ℝ) : Prop :=
  X ⟨0, Nat.zero_lt_succ n⟩ > 0

/-- A vector $X$ is past-directed if its time component $X^0$ is negative. -/
def IsPastDirected {n : ℕ} (X : Fin (n + 1) → ℝ) : Prop :=
  X ⟨0, Nat.zero_lt_succ n⟩ < 0

/-- A vector $V$ is future causal if it is future-directed and causal, i.e.
$V^0 > 0$ and $m(V, V) \leq 0$. -/
def IsFutureCausal {n : ℕ} (V : Fin (n + 1) → ℝ) : Prop :=
  IsFutureDirected V ∧ minkowskiProduct V V ≤ 0

/-- A vector $V$ is past causal if it is past-directed and causal, i.e.
$V^0 < 0$ and $m(V, V) \leq 0$. -/
def IsPastCausal {n : ℕ} (V : Fin (n + 1) → ℝ) : Prop :=
  IsPastDirected V ∧ minkowskiProduct V V ≤ 0

/-- The energy-momentum tensor of a scalar field $\phi$:
$$T_{\mu\nu} \overset{\text{def}}{=} \partial_\mu \phi \, \partial_\nu \phi
  - \tfrac{1}{2} m_{\mu\nu} (m^{-1})^{\alpha\beta} \partial_\alpha \phi \, \partial_\beta \phi.$$
(Definition 1.0.1.) -/
noncomputable def energyMomentumTensor {n : ℕ} (φ : WaveScalarField n)
    (p : WaveSpacetime n) (μ ν : Fin (n + 1)) : ℝ :=
  partialDeriv φ μ p * partialDeriv φ ν p -
    (1/2 : ℝ) * waveMinkowskiMetric n μ ν *
      ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
        minkowskiInverse n α β * partialDeriv φ α p * partialDeriv φ β p

/-- The energy density of a scalar field at a spacetime point:
$\frac{1}{2}\bigl((\partial_t \phi)^2 + |\nabla_x \phi|^2\bigr)$. -/
noncomputable def energyDensity {n : ℕ} (φ : WaveScalarField n) (p : WaveSpacetime n) : ℝ :=
  (1/2 : ℝ) * ((fderiv ℝ (fun s => φ (s, p.2)) p.1 1) ^ 2 +
    ∑ i : Fin n, (fderiv ℝ (fun y => φ (p.1, y)) p.2 (Pi.single i 1)) ^ 2)

/-- The energy of $\phi$ on the ball $B_R(x_0)$ at time $t$:
$\int_{|x - x_0| \leq R} \tfrac{1}{2}(|\partial_t \phi|^2 + |\nabla_x \phi|^2) \, dx$. -/
def energyOnBall {n : ℕ} (φ : WaveScalarField n) (t : ℝ) (x₀ : Fin n → ℝ) (R : ℝ) : ℝ :=
  ∫ x : Fin n → ℝ, if waveEuclidNormSq (x - x₀) ≤ R ^ 2 then energyDensity φ (t, x) else 0


/-- **Lemma 1.0.1 (Dominant Energy Condition for $T_{\mu\nu}$).** For any two causal vectors
$V, W$ that are both future-directed or both past-directed, $T(V, W) = T_{\alpha\beta} V^\alpha W^\beta \geq 0$. -/
noncomputable def divEnergyMomentumTensor {n : ℕ} (φ : WaveScalarField n)
    (p : WaveSpacetime n) (ν : Fin (n + 1)) : ℝ :=
  ∑ μ : Fin (n + 1),
    partialDeriv (fun q =>
      ∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
        minkowskiInverse n μ γ * minkowskiInverse n ν δ *
          energyMomentumTensor φ q γ δ) μ p

/-- The remainder term in the divergence identity for $T^{\mu\nu}$, defined so that
$\partial_\mu T^{\mu\nu}$ equals $(\square_m \phi)(m^{-1})^{\nu\alpha}\partial_\alpha\phi$
plus this remainder. -/
noncomputable def EMT_remainder {n : ℕ} (φ : WaveScalarField n) (p : WaveSpacetime n)
    (ν : Fin (n + 1)) : ℝ :=
  divEnergyMomentumTensor φ p ν -
    waveOp φ p * (∑ α : Fin (n + 1), minkowskiInverse n ν α * partialDeriv φ α p)

/-- The index-lowered components $X_\alpha = m_{\alpha\beta} X^\beta$ of a spacetime
vector field. -/
noncomputable def lowerIndex {n : ℕ} (X : SpacetimeVectorField n) (p : WaveSpacetime n)
    (α : Fin (n + 1)) : ℝ :=
  ∑ β : Fin (n + 1), waveMinkowskiMetric n α β * X p β

/-- **Definition 1.0.2 (Compatible current).** Given a scalar field $\phi$ and a vector
field $X$, the compatible current is the vector field
${}^{(X)} J^\mu \overset{\text{def}}{=} T^{\mu\alpha} X_\alpha$. -/
noncomputable def compatibleCurrent {n : ℕ} (φ : WaveScalarField n)
    (X : SpacetimeVectorField n) (p : WaveSpacetime n) (μ : Fin (n + 1)) : ℝ :=
  ∑ α : Fin (n + 1),
    (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
      minkowskiInverse n μ γ * minkowskiInverse n α δ * energyMomentumTensor φ p γ δ) *
    lowerIndex X p α

/-- The deformation tensor of a vector field $X$:
${}^{(X)} \pi_{\mu\nu} \overset{\text{def}}{=} \tfrac{1}{2}(\partial_\mu X_\nu + \partial_\nu X_\mu)$. -/
noncomputable def deformationTensor {n : ℕ} (X : SpacetimeVectorField n)
    (p : WaveSpacetime n) (μ ν : Fin (n + 1)) : ℝ :=
  (1/2 : ℝ) * (partialDeriv (fun q => lowerIndex X q ν) μ p +
                partialDeriv (fun q => lowerIndex X q μ) ν p)

/-- The divergence $\partial_\mu({}^{(X)} J^\mu)$ of the compatible current. -/
noncomputable def divCompatibleCurrent {n : ℕ} (φ : WaveScalarField n) (X : SpacetimeVectorField n)
    (p : WaveSpacetime n) : ℝ :=
  ∑ μ : Fin (n + 1),
    partialDeriv (fun q => compatibleCurrent φ X q μ) μ p

/-- The auxiliary remainder $\partial_\mu({}^{(X)} J^\mu) - T^{\alpha\beta}\, {}^{(X)}\pi_{\alpha\beta}$,
which vanishes on solutions of the wave equation (Corollary 1.0.3). -/
noncomputable def divEMT_contracted_X {n : ℕ} (φ : WaveScalarField n) (X : SpacetimeVectorField n)
    (p : WaveSpacetime n) : ℝ :=
  divCompatibleCurrent φ X p -
    ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
      (∑ γ : Fin (n + 1), ∑ δ : Fin (n + 1),
        minkowskiInverse n α γ * minkowskiInverse n β δ *
          energyMomentumTensor φ p γ δ) *
      deformationTensor X p α β

end CM14
end
