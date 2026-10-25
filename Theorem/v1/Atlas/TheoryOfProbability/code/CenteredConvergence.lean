/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CenteredConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Independence.Integration
set_option maxHeartbeats 8000000

open MeasureTheory ProbabilityTheory Filter Finset ENNReal


noncomputable section

namespace KolmogorovThreeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

end KolmogorovThreeSeries
end
