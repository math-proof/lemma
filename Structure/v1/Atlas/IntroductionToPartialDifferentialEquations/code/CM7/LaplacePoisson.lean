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
open Real Set MeasureTheory Filter


noncomputable section

namespace LaplacePoisson

/-- A bounded Lipschitz domain in $\mathbb{R}^n$: an open, bounded, nonempty,
connected set whose boundary can be locally straightened by bi-Lipschitz maps.
This is the natural class of domains for the Poisson Dirichlet problem. -/
structure IsLipschitzDomain {n : ℕ} (Ω : Set (Fin n → ℝ)) : Prop where
  isOpen : IsOpen Ω
  isBounded : Bornology.IsBounded Ω
  nonempty : Set.Nonempty Ω
  isConnected : IsConnected Ω
  frontier_nonempty : Set.Nonempty (frontier Ω)
  lipschitz_boundary : ∀ x ∈ frontier Ω, ∃ (U : Set (Fin n → ℝ)),
    IsOpen U ∧ x ∈ U ∧
    ∃ (φ : (Fin n → ℝ) → (Fin n → ℝ)),
      LipschitzWith 1 φ ∧
      ∃ (ψ : (Fin n → ℝ) → (Fin n → ℝ)),
        LipschitzWith 1 ψ ∧
        (∀ y ∈ U, ψ (φ y) = y) ∧ (∀ z ∈ φ '' U, φ (ψ z) = z)

end LaplacePoisson
end
