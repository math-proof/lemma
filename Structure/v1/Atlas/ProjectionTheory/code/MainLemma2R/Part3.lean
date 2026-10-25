/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2R.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Def.v1.Atlas.ProjectionTheory.code.MainLemma2R.Part3


noncomputable section

open MeasureTheory Metric Set Finset

open scoped Classical InnerProductSpace

namespace ProjectionTheory

/-- A frequency decomposition $f = \sum_{r} f_r$ of the tube sum into pieces with
Fourier support in $\{|\xi| \leq 1/r\}$, satisfying a near-orthogonality $L^2$ bound. -/
structure FrequencyDecomposition (S : TubeCollection) where
  f_r : ℝ → (EuclideanSpace ℝ (Fin 2) → ℝ)
  scales : Finset ℝ
  scales_range : ∀ r ∈ scales, r ∈ dyadicScales S.R
  sum_eq : ∀ x, S.tubeSum x = ∑ r ∈ scales, f_r r x
  fourier_support : ∀ r ∈ scales, ∀ ξ : EuclideanSpace ℝ (Fin 2),
    ‖ξ‖ > 1 / r → fourierTransformR2 (f_r r) ξ = 0
  near_orthogonality : ∃ (C_orth : ℝ), 0 < C_orth ∧
    ∑ r ∈ scales, ∫ x, (f_r r x) ^ 2 ≤ C_orth * ∫ x, (S.tubeSum x) ^ 2

end ProjectionTheory
end
