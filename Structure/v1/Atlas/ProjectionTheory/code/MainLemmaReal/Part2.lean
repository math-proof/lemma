/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaReal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.MainLemmaReal
open MeasureTheory Metric Set


noncomputable section

namespace FrequencyDecomposition

/-- Bundle of frequency-decomposition data for the tube sum $f = \sum_T \varphi_T$:
the pieces $f_r$ at dyadic scales, Fourier support inside $\{|\xi| \leq 1/r\}$, and
the per-scale $L^2$ estimate $\|f_r\|_{L^2}^2 \leq C \cdot N_\mathcal{T}(r) \cdot
|\mathcal{T}| / r \cdot R$. -/
structure FrequencyDecompositionData (𝒯 : Finset Tube) (R : ℝ) where
  φ : Tube → ℝ2 → ℂ
  f_r : ℝ → ℝ2 → ℂ
  f : ℝ2 → ℂ := fun x => ∑ T ∈ 𝒯, φ T x
  decomposition : ∀ x, f x = ∑ r ∈ dyadicRange R, f_r r x
  freq_support : ∀ r ∈ dyadicRange R,
    fourierSupport (f_r r) ⊆ Metric.closedBall 0 (1 / r)
  C : ℝ
  hC : 0 < C
  l2_estimate : ∀ r ∈ dyadicRange R,
    l2NormSq (f_r r) ≤ C * (tubeCoveringNumber 𝒯 R r : ℝ) * (𝒯.card : ℝ) * r⁻¹ * R

end FrequencyDecomposition
end
