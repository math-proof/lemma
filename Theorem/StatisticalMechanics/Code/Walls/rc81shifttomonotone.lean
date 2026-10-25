/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc81shifttomonotone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc80structuredwall.Part3
import Def.StatisticalMechanics.Code.Walls.rc81shifttomonotone
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


variable {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem rc81_le_iff (w v : ConfigSpace ι) : rc81_le w v = true ↔ ∀ i, w i = true → v i = true := by
  unfold rc81_le; rw [decide_eq_true_eq]


end StatMech.Walls
