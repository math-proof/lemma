/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedConvexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedIntegralHC.Part2
import Theorem.StatisticalMechanics.Code.Probability.PBiasedConvexity
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

noncomputable def pcx_g (p q t : ℝ) : ℝ :=
  (1 - p) * (1 - p * t) ^ q + p * (1 + (1 - p) * t) ^ q - 1 - 2 * q * (q - 1) * p ^ 2 * (1 - p) ^ 2 * t ^ 2


end StatMech.Probability
