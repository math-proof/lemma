/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc74doubledwall
import Def.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part4
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc75_orbSwap_involutive (i : Fin 2) (c : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))) :
    Function.Involutive (rc75_orbSwap i c) := by
  intro p
  unfold rc75_orbSwap
  by_cases h : p ∈ c ∨ rc75_swapAtF i p ∈ c
  · rw [if_pos h]
    have h2 : rc75_swapAtF i p ∈ c ∨ rc75_swapAtF i (rc75_swapAtF i p) ∈ c := by
      rw [rc75_swapAtF_involutive i p]; tauto
    rw [if_pos h2, rc75_swapAtF_involutive i p]
  · rw [if_neg h, if_neg h]


theorem rc75_orbSwap_bijective (i : Fin 2) (c : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))) :
    Function.Bijective (rc75_orbSwap i c) :=
  (rc75_orbSwap_involutive i c).bijective


end StatMech.Walls
