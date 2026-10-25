/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter11/Defs_and_Props.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Abbrev.v1.Atlas.HighDimensionalStatistics.code.Chapter11.Defs_and_Props
set_option maxHeartbeats 800000


noncomputable section

open scoped SchwartzMap

open MeasureTheory TemperedDistribution Filter ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Chapter11

section Lemma_11_5

/-- The first standard basis vector `(1, 0)` of `ℝ²`. -/
def e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

/-- The second standard basis vector `(0, 1)` of `ℝ²`. -/
def e₂ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1

/-- The Cauchy–Riemann (∂̄) operator `(1/2)(∂_x + i ∂_y)` acting on tempered
distributions on `ℝ²`. -/
def dbarOp : 𝓢'(EuclideanSpace ℝ (Fin 2), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin 2), ℂ) :=
  (1 / 2 : ℂ) • (LineDeriv.lineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin 2), ℂ) e₁
  + Complex.I • LineDeriv.lineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin 2), ℂ) e₂)

/-- The Cauchy kernel `(2π)⁻¹ (x + i y)⁻¹` viewed as a function on `ℝ × ℝ`, a
fundamental solution of the ∂̄ operator. -/
def cauchyRiemannKernel : ℝ × ℝ → ℂ := fun p =>
  (2 * Real.pi)⁻¹ * (↑p.1 + Complex.I * ↑p.2)⁻¹

end Lemma_11_5

section Def_11_8

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E] [(MeasureTheory.volume : Measure E).HasTemperateGrowth]

/-- The singular support of a tempered distribution `u`: the set of points near
which `u` cannot be locally represented by a Schwartz function. -/
def SingularSupport (u : 𝓢'(E, ℂ)) : Set E :=
  {x : E |
    ∀ (φ : E → ℂ), ContDiff ℝ ⊤ φ → HasCompactSupport φ → φ x ≠ 0 →
      TemperedDistribution.smulLeftCLM ℂ φ u ∉
        Set.range (SchwartzMap.toTemperedDistributionCLM E ℂ)}

/-- `F` is a parametrix for `P` if `P F` agrees with `δ₀` modulo a smooth
(Schwartz) error term. -/
def IsParametrix
    (P : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (F : 𝓢'(E, ℂ)) : Prop :=
  P F - TemperedDistribution.delta 0 ∈
    Set.range (SchwartzMap.toTemperedDistributionCLM E ℂ)

/-- `P` is hypoelliptic if it admits a parametrix whose singular support is
contained in `{0}`. -/
def IsHypoelliptic
    (P : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) : Prop :=
  ∃ F : 𝓢'(E, ℂ), IsParametrix E P F ∧ SingularSupport E F ⊆ {0}

end Def_11_8
end Chapter11
end
