/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc74doubledwall
import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc75_swapAtF (i : Fin 2) (p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    ConfigSpace (Fin 2) × ConfigSpace (Fin 2) :=
  (fun j => if j = i then p.2 i else p.1 j, fun j => if j = i then p.1 i else p.2 j)


end StatMech.Walls
