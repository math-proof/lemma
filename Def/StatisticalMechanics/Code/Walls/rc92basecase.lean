/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc92basecase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc80structuredwall.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc92basecase
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


def rc92_cfg3 (b0 b1 b2 : Bool) : ConfigSpace (Fin 3) := ![b0, b1, b2]


def rc92_A0 : Finset (ConfigSpace (Fin 3)) :=
  {rc92_cfg3 false false false, rc92_cfg3 false false true, rc92_cfg3 false true true}


def rc92_A1 : Finset (ConfigSpace (Fin 3)) :=
  {rc92_cfg3 false true false, rc92_cfg3 true false false, rc92_cfg3 true false true}


def rc92_A2 : Finset (ConfigSpace (Fin 3)) :=
  {rc92_cfg3 false false true, rc92_cfg3 false true false, rc92_cfg3 true false false}


end StatMech.Walls
