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
import Def.StatisticalMechanics.Code.Inequalities.ReimerEndpointProve
open Finset MeasureTheory
open scoped NNReal


namespace StatMech

open ConfigSpace

variable {α : Type*}


theorem disjoint_leftBlock_rightBlock : Disjoint (leftBlock (α := α)) (rightBlock (α := α)) := by
  rw [Set.disjoint_left]
  rintro (a | a) hl hr <;>
    simp only [leftBlock, rightBlock, Set.mem_setOf_eq, Sum.isLeft, Sum.isRight,
      Bool.false_eq_true] at hl hr


end StatMech
