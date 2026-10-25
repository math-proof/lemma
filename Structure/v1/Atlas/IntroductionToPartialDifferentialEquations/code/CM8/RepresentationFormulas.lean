/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/RepresentationFormulas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM8.GreenFunctions.Part2
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM8.GreenFunctions
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM8.RepresentationFormulas
open Real Set MeasureTheory


noncomputable section

namespace CM8

/-- The deviation sphere integral $\int (u(\sigma) - u(x)) \nabla_{\hat N}\Phi(x-\sigma)$
tends to $0$ as $\varepsilon \downarrow 0$, obtained by combining the deviation bound with
the oscillation $\to 0$ result. -/
structure GreenFunctionN (n : ℕ) [Fact (2 ≤ n)] (Ω : Set (Fin n → ℝ)) where
  G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  corrector : (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  decomposition : ∀ x y, G x y = FundSolN (x - y) - corrector x y
  boundary_vanish : ∀ x ∈ Ω, ∀ σ ∈ frontier Ω, G x σ = 0
  corrector_harmonic : ∀ x ∈ Ω, ∀ y ∈ Ω, laplacian (corrector x) y = 0
  corrector_boundary : ∀ x ∈ Ω, ∀ σ ∈ frontier Ω, corrector x σ = FundSolN (x - σ)
  corrector_reg : ∀ x ∈ Ω, ContDiffOn ℝ 2 (corrector x) (closure Ω)

end CM8
end
