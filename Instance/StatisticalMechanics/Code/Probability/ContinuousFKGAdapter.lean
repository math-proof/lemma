/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKGAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.ContinuousFKG.Part3
import Def.StatisticalMechanics.Code.Probability.ContinuousFKGAdapter
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech

namespace Probability

set_option linter.unusedSectionVars false


instance (n : ℕ) : IsProbabilityMeasure (cube n) := by
  unfold cube; infer_instance


end Probability
end StatMech
