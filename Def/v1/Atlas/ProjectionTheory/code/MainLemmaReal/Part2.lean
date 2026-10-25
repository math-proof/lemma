/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaReal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ProjectionTheory.code.MainLemmaReal.Part2
open MeasureTheory Metric Set


noncomputable section

namespace FrequencyDecomposition

/-- **Plancherel for the inverse Fourier transform** on $\mathbb{R}^2$:
$\int |\mathcal{F}^{-1}g|^2 = \int |g|^2$ whenever the LHS is integrable. -/
def tubeInteraction (g F : ℝ2 → ℂ) : ℝ :=
  ∫ x, ((starRingEnd ℂ) (g x) * F x).re

end FrequencyDecomposition
end
