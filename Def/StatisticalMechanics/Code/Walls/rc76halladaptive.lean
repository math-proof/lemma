/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part7
import Theorem.StatisticalMechanics.Code.Walls.rc78hallmarriage.Part6
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def swapSet (L : Finset (Fin n)) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    ConfigSpace (Fin n) × ConfigSpace (Fin n) :=
  (fun j => if j ∈ L then p.2 j else p.1 j, fun j => if j ∈ L then p.1 j else p.2 j)


end StatMech.Walls
