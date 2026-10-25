/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Onsager.CellCount


namespace StatMech.Onsager.CellCount

open Finset


theorem cornersOf_card (c : ℤ × ℤ) : (cornersOf c).card = 4 := by
  unfold cornersOf
  rw [Finset.card_insert_of_notMem (by simp only [mem_insert, mem_singleton, Prod.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp only [mem_insert, mem_singleton, Prod.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp only [mem_singleton, Prod.ext_iff]; omega),
      card_singleton]


theorem mem_cornersOf_iff (c v : ℤ × ℤ) :
    v ∈ cornersOf c ↔
      c = v ∨ c = (v.1 - 1, v.2) ∨ c = (v.1, v.2 - 1) ∨ c = (v.1 - 1, v.2 - 1) := by
  obtain ⟨cx, cy⟩ := c
  obtain ⟨vx, vy⟩ := v
  unfold cornersOf
  simp only [mem_insert, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega


end StatMech.Onsager.CellCount
