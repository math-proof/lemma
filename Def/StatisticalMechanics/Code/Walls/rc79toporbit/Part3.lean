/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc78hallmarriage.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc79toporbit.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc79_topTypeF : Fin 2 → Bool × Bool := fun _ => (false, true)


def rc79_complF (w : ConfigSpace (Fin 2)) : ConfigSpace (Fin 2) := fun i => !w i


def rc79_reflInterF (A B : Finset (ConfigSpace (Fin 2))) : Finset (ConfigSpace (Fin 2)) :=
  A.filter (fun a => rc79_complF a ∈ B)


end StatMech.Walls
