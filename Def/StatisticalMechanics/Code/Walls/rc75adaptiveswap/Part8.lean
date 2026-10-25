/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc74doubledwall
import Instance.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc75_cfg (b0 b1 : Bool) : ConfigSpace (Fin 2) := fun i => if i = 0 then b0 else b1


def rc75_wA : Finset (ConfigSpace (Fin 2)) :=
  {rc75_cfg false false, rc75_cfg true false, rc75_cfg false true}


def rc75_wB : Finset (ConfigSpace (Fin 2)) :=
  {rc75_cfg false false, rc75_cfg true false, rc75_cfg true true}


def rc75_gA : Finset (ConfigSpace (Fin 2)) :=
  {rc75_cfg false false, rc75_cfg false true, rc75_cfg true false}


def rc75_gB : Finset (ConfigSpace (Fin 2)) :=
  {rc75_cfg false false, rc75_cfg false true, rc75_cfg true true}


end StatMech.Walls
