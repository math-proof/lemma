/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovPropertyBM.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic.Linarith.NNRealPreprocessor
open MeasureTheory ProbabilityTheory MeasurableSpace Filter
open scoped NNReal ENNReal


noncomputable section

namespace BrownianMotion

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω}

local notation "E" => EuclideanSpace ℝ (Fin d)

end BrownianMotion
end
