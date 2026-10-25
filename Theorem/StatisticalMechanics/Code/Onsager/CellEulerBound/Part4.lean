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
import Def.StatisticalMechanics.Code.Onsager.CellEulerBound.Part4


namespace StatMech.Onsager.CellEulerBound

open Finset SimpleGraph

open StatMech.Euc StatMech.Wad

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler


theorem card_openTopSkeleton_edges (S : Finset Cell) :
    Nat.card (openTopSkeleton S).edgeSet = (regEdges S \ topEdges S).card := by
  rw [Nat.card_congr (openTopEdgeEquiv S), Nat.card_eq_fintype_card, Fintype.card_coe]


theorem regVerts_card_le (S : Finset Cell) (hconn : (openTopSkeleton S).Connected) :
    (regVerts S).card ≤ (regEdges S \ topEdges S).card + 1 := by
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_openTopSkeleton_edges] at h
  exact h


theorem regChi_le_one (S : Finset Cell) (hconn : (openTopSkeleton S).Connected) :
    regChi S ≤ 1 := by
  have hv := regVerts_card_le S hconn
  have hsplit := card_sdiff_add_card (regEdges S) (topEdges S)
  rw [union_eq_left.mpr (topEdges_subset_regEdges S), card_topEdges] at hsplit
  unfold regChi
  push_cast
  omega

theorem eulerChar_le_one (S : Finset Cell) (hconn : (openTopSkeleton S).Connected) :
    eulerChar S ≤ 1 := by
  rw [eulerChar_eq_regChi]
  exact regChi_le_one S hconn

end StatMech.Onsager.CellEulerBound
