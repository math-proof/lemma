/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc78hallmarriage.Part6
import Def.StatisticalMechanics.Code.Walls.rc79toporbit
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc79_mixed_iff_ne (b₁ b₂ : Bool) :
    (b₁ && b₂, b₁ || b₂) = ((false, true) : Bool × Bool) ↔ b₁ ≠ b₂ := by
  cases b₁ <;> cases b₂ <;> simp


theorem rc79_colType_top_iff (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    rc78_colType p = rc79_topType ↔ ∀ i, p.1 i ≠ p.2 i := by
  unfold rc78_colType rc79_topType
  rw [funext_iff]
  constructor
  · intro h i
    exact (rc79_mixed_iff_ne (p.1 i) (p.2 i)).mp (h i)
  · intro h i
    exact (rc79_mixed_iff_ne (p.1 i) (p.2 i)).mpr (h i)


end StatMech.Walls
