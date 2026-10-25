/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellEuler.Part3
import Theorem.StatisticalMechanics.Code.Walls.wadangledefect.Part4
import Def.StatisticalMechanics.Code.Onsager.CellEulerBound.Part2


namespace StatMech.Onsager.CellEulerBound

open Finset SimpleGraph

open StatMech.Euc StatMech.Wad

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler


theorem topEdge_injective : Function.Injective topEdge := by
  rintro ⟨x, y⟩ ⟨u, v⟩ h
  simp only [topEdge, Sym2.eq_iff, Prod.mk.injEq] at h
  rcases h with h | h <;> simp_all <;> omega

theorem card_topEdges (S : Finset Cell) : (topEdges S).card = S.card := by
  exact card_image_of_injective S topEdge_injective

theorem topEdges_subset_regEdges (S : Finset Cell) : topEdges S ⊆ regEdges S := by
  intro e he
  obtain ⟨c, hc, rfl⟩ := mem_image.mp he
  exact mem_biUnion.mpr ⟨c, hc, by simp [topEdge, StatMech.Euc.cellEdges]⟩


end StatMech.Onsager.CellEulerBound
