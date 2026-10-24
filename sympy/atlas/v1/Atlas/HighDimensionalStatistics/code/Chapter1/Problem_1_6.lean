/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Problem_1_6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Def_1_17
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_17
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

open MeasureTheory Real Set Metric
open scoped ENNReal NNReal

noncomputable section

/-- A random vector `X : Ω → ℝ^p` is sub-Gaussian with variance proxy `σ²`
if every unit-norm linear projection `ω ↦ ⟨θ, X ω⟩` is sub-Gaussian with
proxy `σ²`. -/
def IsSubGaussianVec {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin p)) (σsq : ℝ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop :=
  ∀ θ : EuclideanSpace ℝ (Fin p), ‖θ‖ = 1 →
    IsSubGaussian (fun ω => @inner ℝ _ _ θ (X ω)) σsq μ

/-- **Problem 1.6 (Sub-Gaussian supremum over a compact subset of the sphere).**
If `K ⊆ S^{p-1}` has covering numbers bounded by `(C/ε)^d` and `X` is a
sub-Gaussian random vector with proxy `σ²`, then there exist positive
constants `c₁, c₂` such that, for every `δ ∈ (0,1)`, with probability at
least `1 - δ`,
`sup_{θ ∈ K} ⟨θ, X⟩ ≤ c₁ σ √(d log(2p/d)) + c₂ σ √(log(1/δ))`. -/
end
