/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/DoobDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Probability.Martingale.Centering
public import Structure.v1.Atlas.Probability.code.Martingale
open MeasureTheory Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

public section

namespace DoobDecomposition

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {f : ℕ → Ω → ℝ} {ℱ : Filtration ℕ m0}

end DoobDecomposition
