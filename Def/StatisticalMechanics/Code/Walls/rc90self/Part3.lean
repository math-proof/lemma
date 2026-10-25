/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc89nested.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc90self.Part2
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def rc90_Aself : Finset (ConfigSpace (Fin 3)) :=
  {![false, false, false], ![false, false, true], ![false, true, false],
   ![false, true, true], ![true, false, false]}


end StatMech.Walls
