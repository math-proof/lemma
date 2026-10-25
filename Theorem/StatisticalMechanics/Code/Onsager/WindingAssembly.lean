/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.GroundUpWinding.Part4
import Theorem.StatisticalMechanics.Code.Onsager.SplitConstruction
import Theorem.StatisticalMechanics.Code.Onsager.PolygonWalk.Part3
import Def.StatisticalMechanics.Code.Onsager.WindingAssembly


namespace StatMech.Onsager.WindingAssembly

open StatMech.Onsager.SplitConstruction


theorem isAxisAligned_symm {p q : Pt} (h : isAxisAligned p q) : isAxisAligned q p := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm


theorem ccCount_nonneg (V : List Pt) : 0 ≤ ccCount V := Int.natCast_nonneg _


theorem rcCount_nonneg (V : List Pt) : 0 ≤ rcCount V := Int.natCast_nonneg _


theorem structural_chord (V : List Pt) (a b : ℕ)
    (hnd : V.Nodup) (hchain : List.IsChain isAxisAligned V)
    (hwrap : ∀ x ∈ V.getLast?, ∀ y ∈ V.head?, isAxisAligned x y)
    (ha : a < V.length) (hb : b < V.length) (hab : a + 1 < b)
    (hstrict : 0 < a ∨ b + 1 < V.length)
    (hchord : isAxisAligned V[a] V[b]) :
    simplePred (arc V a b) ∧ simplePred (coarc V a b) ∧
      (arc V a b).length < V.length ∧ (coarc V a b).length < V.length := by
  refine ⟨⟨arc_nodup V a b hnd, ?_⟩, ⟨coarc_nodup V a b hnd (by omega), ?_⟩,
    arc_length_lt V a b hb (by omega) hstrict, coarc_length_lt V a b hb hab⟩
  · exact arc_isClosedWalk V a b hb (by omega) hchain (isAxisAligned_symm hchord)
  · exact coarc_isClosedWalk V a b hb (by omega) hchain hwrap hchord


theorem getElem!_eq_getElem (V : List Pt) (a : ℕ) (h : a < V.length) : V[a]! = V[a] := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl


end StatMech.Onsager.WindingAssembly
