/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointLSI.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

noncomputable def tpl_ent (p a b : ℝ) : ℝ :=
  (1 - p) * a * Real.log a + p * b * Real.log b
    - ((1 - p) * a + p * b) * Real.log ((1 - p) * a + p * b)


def tpl_mean (p a b : ℝ) : ℝ := (1 - p) * a + p * b


end StatMech.Probability
