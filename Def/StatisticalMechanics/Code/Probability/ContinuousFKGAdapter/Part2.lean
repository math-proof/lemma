/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKGAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.ContinuousFKG.Part3
import Theorem.StatisticalMechanics.Code.Probability.ContinuousFKGAdapter
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech

namespace Probability

set_option linter.unusedSectionVars false


def restrictCoords {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) : {i // i ∈ S} → ℝ :=
  fun i => x (i : Fin n)


end Probability
end StatMech
