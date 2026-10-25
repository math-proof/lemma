/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc61doubledbutterfly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc60reimerinjection.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc61doubledbutterfly
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc61_upB (i : Fin n) (ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  UV.compression {i} ∅ ℬ


def rc61_dnA (i : Fin n) (𝒜 : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  Down.compression i 𝒜

end StatMech.Walls
