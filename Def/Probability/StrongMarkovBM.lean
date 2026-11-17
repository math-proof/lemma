/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StrongMarkovBM.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Abbrev.v1.Atlas.Probability.code.StoppingTimeContinuous
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped NNReal ENNReal


noncomputable section

namespace BrownianMotion

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The process obtained from `B` by shifting time by the stopping time `T` and
recentering at `B(T)`: `t ↦ B(T + t) - B(T)`. -/
def stoppedShiftedProcess (B : NNReal → Ω → ℝ) (T : Ω → ENNReal) : NNReal → Ω → ℝ :=
  fun t ω => B ((T ω).toNNReal + t) ω - B ((T ω).toNNReal) ω

end BrownianMotion
end
