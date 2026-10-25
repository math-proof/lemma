/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Walls.euceuler
open scoped BigOperators
open Finset


namespace StatMech.Euc

theorem euc_cellVerts_card (c : Cell) : (cellVerts c).card = 4 := by
  obtain ⟨a, b⟩ := c
  unfold cellVerts
  rw [card_insert_of_notMem (by simp), card_insert_of_notMem (by simp),
    card_insert_of_notMem (by simp), card_singleton]


theorem euc_cellEdges_card (c : Cell) : (cellEdges c).card = 4 := by
  obtain ⟨a, b⟩ := c
  unfold cellEdges
  rw [card_insert_of_notMem (by simp), card_insert_of_notMem (by simp),
    card_insert_of_notMem (by simp), card_singleton]


theorem euc_chi_singleton (c : Cell) : regChi {c} = 1 := by
  unfold regChi regVerts regEdges
  rw [singleton_biUnion, singleton_biUnion,
    euc_cellVerts_card, euc_cellEdges_card, card_singleton]
  norm_num


end StatMech.Euc
