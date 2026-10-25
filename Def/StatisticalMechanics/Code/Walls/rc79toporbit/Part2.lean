/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc78hallmarriage.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc79toporbit
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc79_diagTypeF (w : ConfigSpace (Fin 2)) : Fin 2 → Bool × Bool :=
  fun i => (w i, w i)


end StatMech.Walls
