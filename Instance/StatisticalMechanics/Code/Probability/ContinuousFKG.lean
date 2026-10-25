/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Probability.ContinuousFKG.Part2
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech

namespace Probability

set_option linter.unusedSectionVars false


instance : IsProbabilityMeasure unitMeasure := by
  constructor
  rw [unitMeasure, Measure.restrict_apply_univ, Real.volume_Icc]; norm_num


end Probability
end StatMech
