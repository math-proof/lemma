/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/TightnessCompactness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.Defs.Sequences
open MeasureTheory Set Filter Topology

/-- **Prokhorov's theorem (sequential form on ℝ).** A sequence of probability measures `μ n` on
`ℝ` is tight if and only if every subsequence has a further subsequence that converges weakly to
some probability measure `ν`. This is the tightness ↔ relative compactness equivalence for
probability measures on `ℝ`. -/


