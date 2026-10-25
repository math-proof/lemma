/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc7core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc6core.Part3
import Def.StatisticalMechanics.Code.Walls.rc7core
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


section EventCompression

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] in
@[simp] theorem rc7_flip_apply (i : α) (ω : ConfigSpace α) (a : α) :
    rc7_flip i ω a = if a = i then !ω a else ω a := rfl

omit [Fintype α] in
@[simp] theorem rc7_flip_self (i : α) (ω : ConfigSpace α) : rc7_flip i ω i = !ω i := by simp

omit [Fintype α] in

theorem rc7_flip_involutive (i : α) : Function.Involutive (rc7_flip i) := by
  intro ω; funext a; simp only [rc7_flip_apply]; by_cases h : a = i <;> simp [h]

omit [Fintype α] in

theorem rc7_flip_injective (i : α) : Function.Injective (rc7_flip i) :=
  (rc7_flip_involutive i).injective

end EventCompression
end StatMech.Walls
