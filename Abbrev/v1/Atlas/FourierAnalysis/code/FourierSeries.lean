/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/FourierSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open MeasureTheory MeasureTheory.Measure AddCircle
open scoped ENNReal NNReal Convolution


noncomputable section

namespace TorusConvolution

variable {T : ℝ} [hT : Fact (0 < T)]

abbrev mulℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ

end TorusConvolution
end
