/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/SkorokhodRepresentation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
open scoped Topology

/-- **Skorokhod representation theorem.** If a sequence of probability measures `μₙ`
on `ℝ` converges weakly to a probability measure `μ`, then there exist random
variables `Yₙ` and `Z` on a common probability space `(Ω, P)` such that each `Yₙ`
has law `μₙ`, `Z` has law `μ`, and `Yₙ → Z` almost surely. This is the standard
device for converting weak convergence into a.s. convergence. -/


