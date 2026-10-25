/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc74doubledwall
import Def.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part6
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


instance rc75_decidableExistsPlanOrder :
    ∀ (o : List (Fin 2)) (img target : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))),
    Decidable (rc75_existsPlanOrder o img target)
  | [], _, _ => by unfold rc75_existsPlanOrder; infer_instance
  | i :: rest, img, target => by
      unfold rc75_existsPlanOrder
      have : ∀ c, Decidable (rc75_existsPlanOrder rest (rc75_applyChoice i c img) target) :=
        fun c => rc75_decidableExistsPlanOrder rest _ _
      infer_instance


end StatMech.Walls
