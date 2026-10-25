/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc74doubledwall
import Instance.StatisticalMechanics.Code.Walls.rc75adaptiveswap
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc75_existsAdaptivePlan (A B : Finset (ConfigSpace (Fin 2))) : Prop :=
  rc75_existsPlanOrder [0, 1] (rc75_sourceF A B) (rc75_prodF A B) ∨
    rc75_existsPlanOrder [1, 0] (rc75_sourceF A B) (rc75_prodF A B)

end StatMech.Walls
