module
public import Theorem.StatisticalMechanics.Code.Probability.ContinuousFKG.Part3
public import Def.StatisticalMechanics.Code.Probability.ContinuousFKGAdapter
open MeasureTheory
open scoped BigOperators ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKGAdapter.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Probability

set_option linter.unusedSectionVars false


instance (n : ℕ) : IsProbabilityMeasure (cube n) := by
  unfold cube; infer_instance


end Probability
end StatMech
