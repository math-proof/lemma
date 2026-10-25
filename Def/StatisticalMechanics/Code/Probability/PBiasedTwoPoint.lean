/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.BonamiTwoPoint
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

def pbt_g (p q z : ℝ) : ℝ :=
  ((1 - p) + p * z) ^ 2 + (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (z - 1) ^ 2


def pbt_OneVarCore (p q : ℝ) : Prop :=
  ∀ z : ℝ, 0 ≤ z → pbt_g p q z ≤ ((1 - p) + p * z ^ q) ^ (2 / q)


end StatMech.Probability
