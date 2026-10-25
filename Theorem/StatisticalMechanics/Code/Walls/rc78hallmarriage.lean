/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc77configmeasure.Part4
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc78hallmarriage
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc78_swapAt_colType (i : Fin n) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    rc78_colType (swapAt i p) = rc78_colType p := by
  funext j
  unfold rc78_colType swapAt
  by_cases hj : j = i
  · subst hj
    simp only [if_pos]
    rw [Bool.and_comm, Bool.or_comm]
  · simp only [if_neg hj]


end StatMech.Walls
