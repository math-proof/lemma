/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/OptionalStoppingAlt.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Probability.Notation
open MeasureTheory Filter
open scoped ProbabilityTheory ENNReal

public section

/-- Helper lemma: if `f` is a uniformly integrable submartingale adapted to `𝒢` and `N` is a
stopping time, then the sequence `n ↦ f_N · 1_{N ≤ n}` (the contribution to the stopped process
from indices that have already been stopped) is uniformly integrable in `L¹`. -/


