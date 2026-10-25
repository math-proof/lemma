/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.List.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.GetD
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Basic
import Def.v1.Atlas.AlgebraicCombinatorics.code.WreathOrbits.Part6
set_option autoImplicit false


namespace WreathOrbits

variable {m n : ℕ}

lemma mem_canonicalYoung (S : Finset (Fin m × Fin n)) (i : Fin m) (j : Fin n) :
    (i, j) ∈ canonicalYoung S ↔ j.val < (sortedRowSizes S).getD i.val 0 := by
  simp [canonicalYoung, Finset.mem_filter]

lemma canonicalYoung_isLeftJustified (S : Finset (Fin m × Fin n)) :
    IsLeftJustified (canonicalYoung S) := by
  intro i j j' hj hlt
  rw [mem_canonicalYoung] at hj ⊢; omega

lemma filter_lt_card (k : Fin (n + 1)) :
    ((Finset.univ : Finset (Fin n)).filter (fun x : Fin n => (x : ℕ) < (k : ℕ))).card =
      k.val := by
  by_cases hk : k.val < n
  · have : (Finset.univ.filter (fun x : Fin n => (x : ℕ) < (k : ℕ))) =
           Finset.Iio (⟨k.val, hk⟩ : Fin n) := by
      ext ⟨x, hx⟩; simp [Finset.mem_filter, Finset.mem_Iio, Fin.lt_def]
    rw [this, Fin.card_Iio]
  · have hkn : k.val = n := by omega
    have : (Finset.univ.filter (fun x : Fin n => (x : ℕ) < (k : ℕ))) = Finset.univ := by
      ext ⟨x, hx⟩; simp [Finset.mem_filter]; omega
    rw [this, Finset.card_fin, hkn]

lemma rowSize_canonicalYoung (S : Finset (Fin m × Fin n)) (i : Fin m) :
    rowSize (canonicalYoung S) i = (sortedRowSizes S).getD i.val 0 := by
  simp only [rowSize, canonicalYoung]; rw [Finset.filter_filter]
  have h1 : (Finset.univ.filter (fun p : Fin m × Fin n =>
    p.2.val < (sortedRowSizes S).getD p.1.val 0 ∧ p.1 = i)) =
    (Finset.univ.filter (fun p : Fin m × Fin n =>
      p.1 = i ∧ p.2.val < (sortedRowSizes S).getD i.val 0)) := by
    ext ⟨a, b⟩; simp [Finset.mem_filter]
    exact ⟨fun ⟨h1, rfl⟩ => ⟨rfl, h1⟩, fun ⟨rfl, h1⟩ => ⟨h1, rfl⟩⟩
  rw [h1]
  have h2 : (Finset.univ.filter (fun p : Fin m × Fin n =>
      p.1 = i ∧ p.2.val < (sortedRowSizes S).getD i.val 0)) =
    ((Finset.univ : Finset (Fin n)).filter (fun j : Fin n =>
      j.val < (sortedRowSizes S).getD i.val 0)).map
      ⟨Prod.mk i, fun a b h => by simpa using h⟩ := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
               Function.Embedding.coeFn_mk, Prod.mk.injEq]
    exact ⟨fun ⟨rfl, h1⟩ => ⟨b, h1, rfl, rfl⟩,
           fun ⟨j, hlt, ha, hb⟩ => by cases ha; cases hb; exact ⟨rfl, hlt⟩⟩
  rw [h2, Finset.card_map]
  exact filter_lt_card ⟨_, Nat.lt_succ_of_le (getD_le_n S i)⟩

lemma canonicalYoung_antitone (S : Finset (Fin m × Fin n)) :
    Antitone (rowSize (canonicalYoung S)) := by
  intro i₁ i₂ h
  rw [rowSize_canonicalYoung, rowSize_canonicalYoung]
  have hsort := sortedRowSizes_pairwise S
  have h1 : i₁.val < (sortedRowSizes S).length := by
    rw [sortedRowSizes_length]; exact i₁.isLt
  have h2 : i₂.val < (sortedRowSizes S).length := by
    rw [sortedRowSizes_length]; exact i₂.isLt
  rw [List.getD_eq_getElem _ 0 h1, List.getD_eq_getElem _ 0 h2]
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_refl _
  · exact (List.pairwise_iff_getElem.mp hsort i₁.val i₂.val h1 h2 hlt)

lemma canonicalYoung_isGridYoung (S : Finset (Fin m × Fin n)) :
    IsGridYoung (canonicalYoung S) :=
  ⟨canonicalYoung_isLeftJustified S, canonicalYoung_antitone S⟩

lemma finRange_map_getD (l : List ℕ) (hl : l.length = m) :
    (List.finRange m).map (fun i : Fin m => l.getD i.val 0) = l := by
  apply List.ext_getElem (by simp [hl])
  intro k hk1 hk2
  simp [List.getElem_map, List.getElem_finRange]
  rw [List.getElem?_eq_getElem hk2]; simp

lemma map_getD_eq_coe (l : List ℕ) (hl : l.length = m) :
    Finset.univ.val.map (fun i : Fin m => l.getD i.val 0) = ↑l := by
  have : (Finset.univ : Finset (Fin m)).val = ↑(List.finRange m) := by ext x; simp
  rw [this, Multiset.map_coe, finRange_map_getD l hl]

lemma rowSizeMultiset_canonicalYoung (S : Finset (Fin m × Fin n)) :
    rowSizeMultiset (canonicalYoung S) = rowSizeMultiset S := by
  simp only [rowSizeMultiset]
  have h1 : Finset.univ.val.map (rowSize (canonicalYoung S)) =
            Finset.univ.val.map (fun i : Fin m => (sortedRowSizes S).getD i.val 0) := by
    congr 1; funext i; exact rowSize_canonicalYoung S i
  rw [h1, map_getD_eq_coe _ (sortedRowSizes_length S), sortedRowSizes_multiset_eq]

end WreathOrbits
