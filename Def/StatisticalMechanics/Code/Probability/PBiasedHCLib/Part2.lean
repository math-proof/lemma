/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedConvexity.Part2
import Theorem.StatisticalMechanics.Code.Probability.PBiasedHCLib.Part2
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

noncomputable def hclib_K (q t : ℝ) : ℝ :=
  (1 + (q - 1) * t ^ 2) ^ (q / 2) - ((1 + t) ^ q + (1 - t) ^ q) / 2


end StatMech.Probability
