/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/GeneralOptionalStopping.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable

set_option maxHeartbeats 4000000

open MeasureTheory Filter

/-- The stopped value of a process `f : ℕ → Ω → ℝ` at a stopping time `τ : Ω → ℕ∞`
that may take the value `⊤` (infinity). When `τ ω = ⊤`, the value is the limit
`lim_{n → ∞} f n ω`; otherwise it is `f (τ ω) ω`. This extends `stoppedValue` to
allow infinite stopping times, as required for the general optional stopping theorem. -/
noncomputable def stoppedValueExtended {Ω : Type*} [MeasurableSpace Ω]
    (f : ℕ → Ω → ℝ) (τ : Ω → ℕ∞) : Ω → ℝ :=
  fun ω => if τ ω = ⊤ then limUnder atTop (fun n => f n ω)
            else f (τ ω).toNat ω
