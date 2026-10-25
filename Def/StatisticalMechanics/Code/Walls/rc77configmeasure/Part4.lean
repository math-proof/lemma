/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc77configmeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part7
import Theorem.StatisticalMechanics.Code.Walls.rc77configmeasure.Part3
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


def rc77_isDownEvt (A : Finset (ConfigSpace (Fin 2))) : Bool :=
  decide (∀ ω ∈ A, ∀ i : Fin 2, ω i = true → rc77_flip i ω ∈ A)


def rc77_isUpEvt (B : Finset (ConfigSpace (Fin 2))) : Bool :=
  decide (∀ ω ∈ B, ∀ i : Fin 2, ω i = false → rc77_flip i ω ∈ B)

end StatMech.Walls
