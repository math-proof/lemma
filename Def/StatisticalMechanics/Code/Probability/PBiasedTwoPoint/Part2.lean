/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTwoPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.BonamiTwoPoint
import Theorem.StatisticalMechanics.Code.Probability.PBiasedTwoPoint
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

def pbt_lhs (p q u v : ℝ) : ℝ :=
  ((1 - p) * u + p * v) ^ 2 + (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (u - v) ^ 2


end StatMech.Probability
