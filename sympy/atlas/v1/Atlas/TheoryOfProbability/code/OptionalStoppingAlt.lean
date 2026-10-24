/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/OptionalStoppingAlt.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Notation

open MeasureTheory Filter
open scoped ProbabilityTheory ENNReal

/-- Helper lemma: if `f` is a uniformly integrable submartingale adapted to `𝒢` and `N` is a
stopping time, then the sequence `n ↦ f_N · 1_{N ≤ n}` (the contribution to the stopped process
from indices that have already been stopped) is uniformly integrable in `L¹`. -/
