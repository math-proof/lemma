/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/DoobDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Martingale.Centering
import sympy.atlas.v1.Atlas.TheoryOfProbability.code.Martingale

open MeasureTheory Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace DoobDecomposition

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {f : ℕ → Ω → ℝ} {ℱ : Filtration ℕ m0}
