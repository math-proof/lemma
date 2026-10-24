/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StrongMarkovBM.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TheoryOfProbability.code.StoppingTimeContinuous
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped NNReal ENNReal

noncomputable section

namespace BrownianMotion

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The process obtained from `B` by shifting time by the stopping time `T` and
recentering at `B(T)`: `t ↦ B(T + t) - B(T)`. -/
def stoppedShiftedProcess (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0∞) : ℝ≥0 → Ω → ℝ :=
  fun t ω => B ((T ω).toNNReal + t) ω - B ((T ω).toNNReal) ω

end BrownianMotion

open BrownianMotion in
/-- **Strong Markov property for Brownian motion** (Lecture 39). Given a real-valued
Brownian motion `B` adapted to `ℱ` with `B 0 = 0`, independent Gaussian increments and
continuous paths, and an almost-surely finite stopping time `T`, the shifted/recentered
process `t ↦ B(T + t) - B(T)` is independent of `ℱ_T`, starts at `0`, has the same
Gaussian increment distribution as `B`, and has continuous paths almost surely. -/
