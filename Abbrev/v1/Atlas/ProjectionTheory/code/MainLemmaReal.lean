/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaReal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open MeasureTheory Metric Set


noncomputable section

namespace FrequencyDecomposition

/-- Short alias for the Euclidean plane $\mathbb{R}^2$. -/
abbrev ℝ2 := EuclideanSpace ℝ (Fin 2)

end FrequencyDecomposition
end
