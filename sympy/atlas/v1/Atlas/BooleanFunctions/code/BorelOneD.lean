/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/BorelOneD.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import sympy.atlas.v1.Atlas.BooleanFunctions.code.GaussianStability
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Sheppard
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Sheppard

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace GaussianStability

def thresholdAtLevel (t : ℝ) : ℝ → ℝ :=
  fun x => if x ≥ t then (1 : ℝ) else -1

def thresholdFn (c : ℝ) : ℝ → ℝ :=
  thresholdAtLevel (Classical.epsilon (fun t =>
    ∫ x, thresholdAtLevel t x ∂(gaussianReal 0 1) = c))
