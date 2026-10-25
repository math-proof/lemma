/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PolygonWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Onsager.PolygonWalk


namespace StatMech.Onsager.PolygonWalk

theorem cross_unit_mem (a b : Pt) (ha : isUnitDir a) (hb : isUnitDir b) :
    cross a b = -1 ∨ cross a b = 0 ∨ cross a b = 1 := by
  rcases ha with h | h | h | h <;> rcases hb with h' | h' | h' | h' <;>
    subst h <;> subst h' <;> simp only [cross] <;> norm_num


theorem cross_swap (a b : Pt) : cross b a = - cross a b := by
  simp only [cross]; ring


theorem cross_self (a : Pt) : cross a a = 0 := by simp only [cross]; ring


theorem balance_split (c r c₁ r₁ c₂ r₂ : ℤ)
    (hc : c₁ + c₂ = c + 3) (hr : r₁ + r₂ = r - 1) :
    (c - r) = (c₁ - r₁) + (c₂ - r₂) - 4 := by omega


end StatMech.Onsager.PolygonWalk
