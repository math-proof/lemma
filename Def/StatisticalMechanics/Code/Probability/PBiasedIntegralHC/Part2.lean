/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedIntegralHC.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedTwoPoint.Part3
import Theorem.StatisticalMechanics.Code.Probability.PBiasedIntegralHC
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

def pih_KEY (p q : ℝ) : Prop :=
  ∀ z : ℝ, 0 ≤ z →
    (q / 2) * (pih_m p z) ^ (q - 2) * pih_V p q z ≤ (1 - p) + p * z ^ q - (pih_m p z) ^ q


end StatMech.Probability
