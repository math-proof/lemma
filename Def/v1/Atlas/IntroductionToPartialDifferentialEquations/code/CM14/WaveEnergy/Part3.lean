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
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM14.WaveEnergy
open MeasureTheory Set Finset Classical


noncomputable section

namespace CM14

/-- The outward-pointing unit normal covector $\hat N$ to the boundary of a domain
$\Omega \subset \mathbb{R}^{1+n}$. Treated as an `opaque` primitive in this development. -/
opaque outwardUnitNormal {n : ℕ} (Ω : Set (WaveSpacetime n))
    (σ : WaveSpacetime n) : Fin (n + 1) → ℝ

/-- The surface measure on the boundary $\partial\Omega$, defined as the $n$-dimensional
Hausdorff measure restricted to the topological frontier of $\Omega$. -/
noncomputable def surfaceMeasure {n : ℕ} (Ω : Set (WaveSpacetime n)) :
    Measure (WaveSpacetime n) :=
  (Measure.hausdorffMeasure n).restrict (frontier Ω)

/-- The boundary flux integral $\int_{\partial \Omega} \hat N_\alpha\, {}^{(X)} J^\alpha\, d\sigma$
of the compatible current ${}^{(X)} J$ through $\partial\Omega$. -/
noncomputable def boundaryFluxIntegral {n : ℕ} (φ : WaveScalarField n)
    (X : SpacetimeVectorField n) (Ω : Set (WaveSpacetime n)) : ℝ :=
  ∫ σ in frontier Ω,
    (∑ α : Fin (n + 1), outwardUnitNormal Ω σ α * compatibleCurrent φ X σ α)
    ∂(surfaceMeasure Ω)

/-- **Theorem 1.1 (Divergence Theorem).** For a solution $\phi$ of the wave equation on a
regular domain $\Omega \subset \mathbb{R}^{1+n}$, the boundary flux of the compatible
current equals the bulk integral of its divergence:
$\int_{\partial\Omega} \hat N_\alpha\, {}^{(X)}J^\alpha\, d\sigma = \int_\Omega \partial_\mu({}^{(X)}J^\mu)\, dt\, d^n x$. -/
def truncatedBackwardsCone {n : ℕ} (x₀ : Fin n → ℝ) (R t₀ t₁ : ℝ) :
    Set (WaveSpacetime n) :=
  { p | t₀ ≤ p.1 ∧ p.1 ≤ t₁ ∧ waveEuclidNormSq (p.2 - x₀) ≤ (R - p.1) ^ 2 }

/-- The constant past-directed timelike Killing vector field $X^\mu = -\delta_0^\mu$. -/
def pastTimelikeKillingField (n : ℕ) : SpacetimeVectorField n :=
  fun _ μ => if μ.val = 0 then -1 else 0

/-- The lateral (null) mantle of the truncated backwards cone:
$\{(t, x) \mid 0 \leq t \leq t,\ |x - x_0| = R - t\}$. -/
def coneMantle {n : ℕ} (x₀ : Fin n → ℝ) (R : ℝ) (t : ℝ) : Set (WaveSpacetime n) :=
  { p | 0 ≤ p.1 ∧ p.1 ≤ t ∧ waveEuclidNormSq (p.2 - x₀) = (R - p.1) ^ 2 }

/-- The flux of the compatible current associated to the past-timelike Killing field through
the lateral mantle of the truncated backwards cone. -/
noncomputable def mantleFlux {n : ℕ} (φ : WaveScalarField n)
    (x₀ : Fin n → ℝ) (R t : ℝ) : ℝ :=
  let Ω := interior (truncatedBackwardsCone x₀ R 0 t)
  let X := pastTimelikeKillingField n
  let M := coneMantle x₀ R t
  ∫ σ in M, (∑ α : Fin (n + 1), outwardUnitNormal Ω σ α * compatibleCurrent φ X σ α)
    ∂(Measure.hausdorffMeasure n)

/-- The boundary $\partial\Omega$ of the truncated backwards cone decomposes into top face,
base face, and mantle, and accordingly the boundary flux integral splits as the sum of the
three corresponding face integrals. -/
def raiseIndex {n : ℕ} (N : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun γ => ∑ μ : Fin (n + 1), minkowskiInverse n γ μ * N μ

/-- **Corollary 2.0.4 (Uniqueness).** Two $C^2$ solutions $\phi_1, \phi_2$ to the wave
equation with the same initial data $(\phi, \partial_t \phi)|_{t=0}$ on $\overline{B_R(x_0)}$
agree on the solid backwards light cone
$\mathcal{C}_{x_0; R} = \{(t, x) \mid 0 \leq t \leq R,\ |x - x_0| \leq R - t\}$. -/
def IsDevelopment {n : ℕ} (S : Set (Fin n → ℝ)) (Ω : Set (WaveSpacetime n)) : Prop :=
  (∀ p ∈ Ω, p.1 ≥ 0) ∧
  ∀ (φ₁ φ₂ : WaveScalarField n),
    (∀ p, waveOp φ₁ p = 0) →
    (∀ p, waveOp φ₂ p = 0) →
    ContDiff ℝ 2 φ₁ →
    ContDiff ℝ 2 φ₂ →
    (∀ x ∈ S, φ₁ (0, x) = φ₂ (0, x)) →
    (∀ x ∈ S, fderiv ℝ (fun s => φ₁ (s, x)) 0 1 = fderiv ℝ (fun s => φ₂ (s, x)) 0 1) →
    ∀ p ∈ Ω, φ₁ p = φ₂ p

/-- The past-development variant of `IsDevelopment`: $\Omega \subset \{t \leq 0\}$ such that
identical initial data on $S$ force agreement throughout $\Omega$. -/
def IsPastDevelopment {n : ℕ} (S : Set (Fin n → ℝ)) (Ω : Set (WaveSpacetime n)) : Prop :=
  (∀ p ∈ Ω, p.1 ≤ 0) ∧
  ∀ (φ₁ φ₂ : WaveScalarField n),
    (∀ p, waveOp φ₁ p = 0) →
    (∀ p, waveOp φ₂ p = 0) →
    ContDiff ℝ 2 φ₁ →
    ContDiff ℝ 2 φ₂ →
    (∀ x ∈ S, φ₁ (0, x) = φ₂ (0, x)) →
    (∀ x ∈ S, fderiv ℝ (fun s => φ₁ (s, x)) 0 1 = fderiv ℝ (fun s => φ₂ (s, x)) 0 1) →
    ∀ p ∈ Ω, φ₁ p = φ₂ p

/-- **Definition 3.0.4 (Maximal future development).** The maximal future development of $S$,
denoted $\mathcal{D}^+(S)$, is the union of all future developments of $S$. -/
def maximalDevelopment {n : ℕ} (S : Set (Fin n → ℝ)) : Set (WaveSpacetime n) :=
  ⋃₀ { Ω | IsDevelopment S Ω }

/-- The maximal past development of $S$, $\mathcal{D}^-(S)$, defined as the union of all
past developments of $S$. -/
def maximalPastDevelopment {n : ℕ} (S : Set (Fin n → ℝ)) : Set (WaveSpacetime n) :=
  ⋃₀ { Ω | IsPastDevelopment S Ω }

/-- The (total) maximal development of $S$: $\mathcal{D}^+(S) \cup \mathcal{D}^-(S)$. -/
def maximalTotalDevelopment {n : ℕ} (S : Set (Fin n → ℝ)) : Set (WaveSpacetime n) :=
  maximalDevelopment S ∪ maximalPastDevelopment S

/-- **Definition 3.0.5 (Domain of dependence).** A set $S \subset \mathbb{R}^{1+n}$ is a
domain of dependence for $\Omega$ if any two $C^2$ wave-equation solutions which agree
together with all of their first-order partial derivatives on $S$ also agree on $\Omega$. -/
def IsDomainOfDependence {n : ℕ} (Ω : Set (WaveSpacetime n)) (S : Set (WaveSpacetime n)) : Prop :=
  ∀ (φ₁ φ₂ : WaveScalarField n),
    (∀ p, waveOp φ₁ p = 0) →
    (∀ p, waveOp φ₂ p = 0) →
    ContDiff ℝ 2 φ₁ →
    ContDiff ℝ 2 φ₂ →
    (∀ p ∈ S, φ₁ p = φ₂ p) →
    (∀ p ∈ S, ∀ μ : Fin (n + 1), partialDeriv φ₁ μ p = partialDeriv φ₂ μ p) →
    ∀ p ∈ Ω, φ₁ p = φ₂ p

/-- **Definition 3.0.6 (Range of influence).** The range of influence of $S$ is the set of
all spacetime points $p$ where some pair of $C^2$ wave-equation solutions, which agree
together with their partial derivatives off of $S$, nevertheless disagree at $p$. -/
def rangeOfInfluence {n : ℕ} (S : Set (WaveSpacetime n)) : Set (WaveSpacetime n) :=
  { p | ¬ ∀ (φ₁ φ₂ : WaveScalarField n),
      (∀ q, waveOp φ₁ q = 0) →
      (∀ q, waveOp φ₂ q = 0) →
      ContDiff ℝ 2 φ₁ →
      ContDiff ℝ 2 φ₂ →
      (∀ q, q ∉ S → φ₁ q = φ₂ q) →
      (∀ q, q ∉ S → ∀ μ : Fin (n + 1), partialDeriv φ₁ μ q = partialDeriv φ₂ μ q) →
      φ₁ p = φ₂ p }

end CM14
end
