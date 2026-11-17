/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CenteredConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.BorelCantelli
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Independence.Integration
set_option maxHeartbeats 8000000

open MeasureTheory ProbabilityTheory Filter Finset ENNReal

public section

noncomputable section

namespace KolmogorovThreeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

end KolmogorovThreeSeries
end
