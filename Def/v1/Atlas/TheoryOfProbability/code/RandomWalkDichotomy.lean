/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/RandomWalkDichotomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.MeasureSpace
open MeasureTheory ProbabilityTheory Filter Finset Topology


noncomputable section

/-- The `n`-th partial sum `Sₙ(ω) = ∑_{i < n} Xᵢ(ω)` of the sequence of random variables `X`,
viewed as a random walk on `ℝ`. -/
def randomWalkPartialSum {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, X i ω

section RandomWalkDichotomy

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

variable (X : ℕ → Ω → ℝ)

/-- The random walk *drifts to `+∞`*: almost surely `Sₙ → +∞` as `n → ∞`. -/
def DriftsToTop : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n => randomWalkPartialSum X n ω) atTop atTop

/-- The random walk *drifts to `-∞`*: almost surely `Sₙ → -∞` as `n → ∞`. -/
def DriftsToBot : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n => randomWalkPartialSum X n ω) atTop atBot

/-- The random walk *oscillates*: almost surely `limsup Sₙ = +∞` and `liminf Sₙ = -∞`. -/
def Oscillates : Prop :=
  ∀ᵐ ω ∂μ, limsup (fun n => (randomWalkPartialSum X n ω : EReal)) atTop = ⊤ ∧
             liminf (fun n => (randomWalkPartialSum X n ω : EReal)) atTop = ⊥

/-- The random walk *converges to a finite limit*: almost surely there exists `l ∈ ℝ`
with `Sₙ → l`. In the i.i.d. dichotomy this corresponds to the degenerate case where
each `Xᵢ = 0`. -/
def ConvergesFinite : Prop :=
  ∀ᵐ ω ∂μ, ∃ l : ℝ, Tendsto (fun n => randomWalkPartialSum X n ω) atTop (𝓝 l)

end RandomWalkDichotomy
end
