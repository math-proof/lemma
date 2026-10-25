/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc28cylrec.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc27recursion.Part2
import Def.StatisticalMechanics.Code.Walls.rc28cylrec.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in

theorem rc28_reflEComp_eq (n : ℕ) (E : Finset (Fin n)) (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc28_reflEComp n E 𝒜 ℬ = rc14_reflE E 𝒜 ℬ := by
  ext S
  rw [rc28_reflEComp, rc14_reflE, Finset.mem_filter, Finset.mem_filter, decide_eq_true_eq]


end StatMech.Walls
