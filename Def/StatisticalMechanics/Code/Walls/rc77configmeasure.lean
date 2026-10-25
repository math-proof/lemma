/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc77configmeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part7
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


def rc77_flip (i : Fin 2) (ω : ConfigSpace (Fin 2)) : ConfigSpace (Fin 2) :=
  fun j => if j = i then !ω j else ω j


def rc77_downEvt (i : Fin 2) (A : Finset (ConfigSpace (Fin 2))) : Finset (ConfigSpace (Fin 2)) :=
  A.image (fun ω => if ω i = true ∧ rc77_flip i ω ∉ A then rc77_flip i ω else ω)


def rc77_upEvt (i : Fin 2) (B : Finset (ConfigSpace (Fin 2))) : Finset (ConfigSpace (Fin 2)) :=
  B.image (fun ω => if ω i = false ∧ rc77_flip i ω ∉ B then rc77_flip i ω else ω)


def rc77_wA : Finset (ConfigSpace (Fin 2)) :=
  {rc75_cfg false false, rc75_cfg false true}


def rc77_wB : Finset (ConfigSpace (Fin 2)) :=
  {rc75_cfg false true, rc75_cfg true false}

end StatMech.Walls
