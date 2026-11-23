/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Tactic
public import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM9.PoissonHarnackLiouville
public import Theorem.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM9.PoissonHarnackLiouville
public import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM7.LaplacePoisson.Part2
open Real Set MeasureTheory Filter


public noncomputable section

namespace LaplacePoisson

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

end LaplacePoisson
end
