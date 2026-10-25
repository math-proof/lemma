/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc74doubledwall
import Def.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part5
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc75_applyChoice_card (i : Fin 2) (c : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)))
    (img : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))) :
    (rc75_applyChoice i c img).card = img.card := by
  unfold rc75_applyChoice
  exact Finset.card_image_of_injective img (rc75_orbSwap_bijective i c).injective


end StatMech.Walls
