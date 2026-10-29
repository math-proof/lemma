/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InhomogeneousProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InfiniteBK
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


namespace StatMech

variable {E : Type*}


theorem bernoulliMeasure_congr {p q : NNReal} (hp : p ≤ 1) (hq : q ≤ 1)
    (h : p = q) : bernoulliMeasure p hp = bernoulliMeasure q hq := by
  subst q
  rfl


end StatMech
