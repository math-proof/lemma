/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc74doubledwall
import Def.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part3
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc75_swapAtF_involutive (i : Fin 2) : Function.Involutive (rc75_swapAtF i) := by
  intro p
  unfold rc75_swapAtF
  ext j <;> simp only [] <;> split_ifs with h <;> subst_vars <;> rfl


end StatMech.Walls
