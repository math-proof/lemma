/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Grade
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Linarith
import Def.v1.Atlas.AlgebraicCombinatorics.code.HasseWalks


namespace HasseWalks

structure HasseWalk (steps : List HStep) (start target : YoungDiagram) : Type where
  diagram : Fin (steps.length + 1) → YoungDiagram
  start_eq : diagram ⟨0, Nat.zero_lt_succ _⟩ = start
  target_eq : diagram ⟨steps.length, Nat.lt_succ_of_le le_rfl⟩ = target
  step_up : ∀ (i : Fin steps.length), steps[i] = HStep.U →
    diagram ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
    diagram ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  step_down : ∀ (i : Fin steps.length), steps[i] = HStep.D →
    diagram ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ⋖
    diagram ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

end HasseWalks
