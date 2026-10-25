/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Walls.euceuler.Part2
open scoped BigOperators
open Finset


namespace StatMech.Euc

theorem euc_regVerts_insert (c : Cell) (K : Finset Cell) :
    regVerts (insert c K) = cellVerts c ∪ regVerts K := by
  unfold regVerts; rw [biUnion_insert]


theorem euc_regEdges_insert (c : Cell) (K : Finset Cell) :
    regEdges (insert c K) = cellEdges c ∪ regEdges K := by
  unfold regEdges; rw [biUnion_insert]


theorem euc_regVerts_card_insert (c : Cell) (K : Finset Cell) :
    (regVerts (insert c K)).card = newVerts c K + (regVerts K).card := by
  rw [euc_regVerts_insert, newVerts, ← card_sdiff_add_card (cellVerts c) (regVerts K)]


theorem euc_regEdges_card_insert (c : Cell) (K : Finset Cell) :
    (regEdges (insert c K)).card = newEdges c K + (regEdges K).card := by
  rw [euc_regEdges_insert, newEdges, ← card_sdiff_add_card (cellEdges c) (regEdges K)]


theorem euc_chi_insert (c : Cell) (K : Finset Cell) (hc : c ∉ K) :
    regChi (insert c K)
      = regChi K + ((newVerts c K : ℤ) - (newEdges c K : ℤ) + 1) := by
  unfold regChi
  rw [euc_regVerts_card_insert, euc_regEdges_card_insert, card_insert_of_notMem hc]
  push_cast
  ring


theorem euc_chi_attach (c : Cell) (K : Finset Cell) (hc : c ∉ K)
    (harc : newEdges c K = newVerts c K + 1) :
    regChi (insert c K) = regChi K := by
  rw [euc_chi_insert c K hc, harc]
  push_cast; ring


end StatMech.Euc
