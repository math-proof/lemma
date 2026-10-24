/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StrongMarkovChain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import sympy.atlas.v1.Atlas.TheoryOfProbability.code.StoppingTime
import sympy.atlas.v1.Atlas.TheoryOfProbability.code.MarkovPropertyChain
import Lemma.Measure.Atlas.v1.TheoryOfProbability.code.MarkovPropertyChain

open MeasureTheory ProbabilityTheory

/-- Shift a path `ω : ℕ → S` by the stopping time `T ω`: the resulting path at index `k`
is `ω (T ω + k)`. -/
def stoppedPathShift {S : Type*} (T : (ℕ → S) → ℕ) : (ℕ → S) → (ℕ → S) :=
  fun ω k => ω (T ω + k)
