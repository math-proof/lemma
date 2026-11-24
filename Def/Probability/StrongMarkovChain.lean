module
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
public import Structure.v1.Atlas.Probability.code.StoppingTime
public import Def.Probability.MarkovPropertyChain.Part2
public import Theorem.Measure.Atlas.v1.Probability.code.MarkovPropertyChain
open MeasureTheory ProbabilityTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StrongMarkovChain.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-- Shift a path `ω : ℕ → S` by the stopping time `T ω`: the resulting path at index `k`
is `ω (T ω + k)`. -/
def stoppedPathShift {S : Type*} (T : (ℕ → S) → ℕ) : (ℕ → S) → (ℕ → S) :=
  fun ω k => ω (T ω + k)

