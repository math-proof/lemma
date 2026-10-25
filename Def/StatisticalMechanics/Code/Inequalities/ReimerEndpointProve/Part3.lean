/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerEndpointProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerEndpointProve.Part2
open Finset MeasureTheory
open scoped NNReal


namespace StatMech

open ConfigSpace

variable {α : Type*}


section Weighted

variable [Fintype α] [DecidableEq α]


def doubleWeight (w : α → Bool → ℝ) : (α ⊕ α) → Bool → ℝ := Sum.elim w w

end Weighted
end StatMech
