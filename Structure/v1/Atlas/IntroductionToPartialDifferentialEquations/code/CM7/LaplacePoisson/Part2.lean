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
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM7.LaplacePoisson
open Real Set MeasureTheory Filter


noncomputable section

namespace LaplacePoisson

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

end LaplacePoisson
end
