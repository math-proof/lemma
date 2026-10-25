/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part7
import Theorem.StatisticalMechanics.Code.Walls.rc78hallmarriage.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc76halladaptive.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc76_source (A B : Finset (ConfigSpace (Fin 2))) :
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  rc75_sourceF A B


def rc76_target (A B : Finset (ConfigSpace (Fin 2))) :
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  rc75_prodF A B


def rc76_wall (A B : Finset (ConfigSpace (Fin 2))) : Prop :=
  2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card

end StatMech.Walls
