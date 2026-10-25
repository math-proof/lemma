/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellCount.Part2
import Def.StatisticalMechanics.Code.Onsager.CellEuler.Part3


namespace StatMech.Onsager.CellEuler

open Finset StatMech.Onsager.CellCount


theorem edgesOf_card (c : ℤ × ℤ) : (edgesOf c).card = 4 := by
  unfold edgesOf
  rw [Finset.card_insert_of_notMem (by simp only [mem_insert, mem_singleton, Prod.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp only [mem_insert, mem_singleton, Prod.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp only [mem_singleton, Prod.ext_iff]; omega),
      card_singleton]


theorem cellEdges_insert (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    cellEdges (insert c S) = edgesOf c ∪ cellEdges S := by
  unfold cellEdges; rw [Finset.biUnion_insert]


theorem cellEdges_singleton (c : ℤ × ℤ) : cellEdges ({c} : Finset (ℤ × ℤ)) = edgesOf c := by
  unfold cellEdges; rw [Finset.singleton_biUnion]


theorem eulerChar_singleton (c : ℤ × ℤ) : eulerChar ({c} : Finset (ℤ × ℤ)) = 1 := by
  unfold eulerChar
  rw [cellVerts_singleton, cellEdges_singleton, cornersOf_card, edgesOf_card, Finset.card_singleton]
  ring


theorem card_union_sub (A B : Finset (ℤ × ℤ)) :
    ((A ∪ B).card : ℤ) - B.card = ((A \ B).card : ℤ) := by
  have hEq : A ∪ B = B ∪ (A \ B) := by
    rw [Finset.union_sdiff_self_eq_union, Finset.union_comm]
  rw [hEq, Finset.card_union_of_disjoint (Finset.sdiff_disjoint).symm]
  push_cast; ring


theorem eulerChar_insert_vertexDelta (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    ((cellVerts (insert c S)).card : ℤ) - (cellVerts S).card
      = ((cornersOf c \ cellVerts S).card : ℤ) := by
  rw [cellVerts_insert]; exact card_union_sub (cornersOf c) (cellVerts S)


theorem eulerChar_insert_edgeDelta (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    ((cellEdges (insert c S)).card : ℤ) - (cellEdges S).card
      = ((edgesOf c \ cellEdges S).card : ℤ) := by
  rw [cellEdges_insert]; exact card_union_sub (edgesOf c) (cellEdges S)


theorem eulerChar_insert (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∉ S) :
    eulerChar (insert c S)
      = eulerChar S + (((cornersOf c \ cellVerts S).card : ℤ)
          - (edgesOf c \ cellEdges S).card + 1) := by
  have hV := eulerChar_insert_vertexDelta S c
  have hE := eulerChar_insert_edgeDelta S c
  unfold eulerChar
  rw [Finset.card_insert_of_notMem hc]
  push_cast at hV hE ⊢
  linarith [hV, hE]

end StatMech.Onsager.CellEuler
