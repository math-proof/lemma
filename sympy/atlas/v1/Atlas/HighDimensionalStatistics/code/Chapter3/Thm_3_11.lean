/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_11.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Def_3_10
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Def_3_10

open Real MeasureTheory Set

namespace Chapter3

/-- The Sobolev ellipsoid `Θ(β, Q)` defined as the set of sequences `θ : ℕ → ℝ`
all of whose finite partial sums `∑ aⱼ² θⱼ²` (with `aⱼ` the Sobolev coefficients)
are bounded by `Q`. -/
def SobolevEllipsoidInf (β Q : ℝ) : Set (ℕ → ℝ) :=
  {θ | ∀ M : ℕ,
    ∑ j : Fin M, (sobolevCoeff β (j.val + 1)) ^ 2 * (θ (j.val + 1)) ^ 2 ≤ Q}

/-- The companion map on `ℕ`: pairs `2k+1 ↔ 2k+2`, fixing `0`. Used to bound
a sequence by sums of paired terms. -/
def companion : ℕ → ℕ
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 1 then n + 2 else n
