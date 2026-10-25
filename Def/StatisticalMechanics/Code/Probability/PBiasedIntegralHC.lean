/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedIntegralHC.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedTwoPoint.Part3
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

def pih_m (p z : ℝ) : ℝ := (1 - p) + p * z


def pih_V (p q z : ℝ) : ℝ := 4 * (q - 1) * p ^ 2 * (1 - p) ^ 2 * (z - 1) ^ 2


end StatMech.Probability
