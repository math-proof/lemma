/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedConvexity.Part2
import Theorem.StatisticalMechanics.Code.Probability.PBiasedHCLib
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

def hclib_BracketResidue (q : ℝ) : Prop :=
  ∀ t : ℝ, |t| ≤ 1 →
    ((1 + t) ^ (q - 2) + (1 - t) ^ (q - 2)) / 2
      ≤ (1 + (q - 1) * t ^ 2) ^ ((q - 4) / 2) * (1 + (q - 1) ^ 2 * t ^ 2)


end StatMech.Probability
