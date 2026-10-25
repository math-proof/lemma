/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StrongMarkovBMGoal98.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Structure.v1.Atlas.TheoryOfProbability.code.StrongMarkovBMGoal98
set_option maxHeartbeats 8000000

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped NNReal ENNReal


noncomputable section

namespace StrongMarkovBMGoal98

variable {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ}

/-- The path of `B` shifted by the (possibly infinite) stopping time `S`: at sample `ω`
returns the path `t ↦ B (S ω + t) ω`. -/
def pathShiftAtStopping (B : ℝ≥0 → Ω → Rd d) (S : Ω → ℝ≥0∞) (ω : Ω) :
    ℝ≥0 → Rd d :=
  fun t => B ((S ω).toNNReal + t) ω

/-- The function `(t, x) ↦ E_x[Y t (B_·)]`: integrating the time-indexed path
functional `Y` against the Brownian motion law started from `x`. -/
def bmExpectation (B : ℝ≥0 → Ω → Rd d) (P : Rd d → Measure Ω)
    (Y : ℝ≥0 → (ℝ≥0 → Rd d) → ℝ) (t : ℝ≥0) (x : Rd d) : ℝ :=
  ∫ ω, Y t (fun s => B s ω) ∂(P x)

end StrongMarkovBMGoal98
end
