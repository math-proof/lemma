/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc94extra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc93extra.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc94extra
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def rc94_InterCoverA (A B : Finset (ConfigSpace ι)) : Prop :=
  ∀ w ∈ A ∩ B, rc80_compl w ∈ A


end StatMech.Walls
