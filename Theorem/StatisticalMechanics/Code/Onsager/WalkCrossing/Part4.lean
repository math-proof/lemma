/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.BaseCase
import Theorem.StatisticalMechanics.Code.Onsager.NoDoubleWind
import Def.StatisticalMechanics.Code.Onsager.WalkCrossing.Part4


namespace StatMech.Onsager.WalkCrossing

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager.NoDoubleWind

variable {n : ℕ} [NeZero n]


theorem rayCross_le_fullLineCross (d : Fin n → Fin 4) (m qx : ℤ) :
    rayCross d m qx ≤ fullLineCross d m := by
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, hk.2.1, hk.2.2.2⟩

end StatMech.Onsager.WalkCrossing
