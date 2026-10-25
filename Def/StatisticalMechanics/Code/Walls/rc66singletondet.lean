/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc66singletondet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc65marriagetwo.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc66singletondet
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc66_wA : Finset (Finset (Fin 2)) := {∅, {0}, {1}}


def rc66_wB : Finset (Finset (Fin 2)) := {∅, {0}, {0, 1}}


end StatMech.Walls
