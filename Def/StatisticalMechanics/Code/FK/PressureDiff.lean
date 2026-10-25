/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PressureDiff.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdgeMarginal.Part2
import Theorem.StatisticalMechanics.Code.FK.Uniqueness
open Set Filter Topology

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

section ConvexFunction

variable {g : ℝ → ℝ}


noncomputable def pressureRightDeriv (g : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin g (Ioi x) x


noncomputable def pressureLeftDeriv (g : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin g (Iio x) x


end ConvexFunction
end FK
end StatMech
