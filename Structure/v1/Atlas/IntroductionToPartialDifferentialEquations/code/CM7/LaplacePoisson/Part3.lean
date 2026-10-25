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
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM7.LaplacePoisson.Part2
open Real Set MeasureTheory Filter


noncomputable section

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
