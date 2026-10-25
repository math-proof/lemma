/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
import Def.StatisticalMechanics.Code.Walls.wcbcolumnbridge.Part4
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

theorem wcb_columnOrder_permutes_signedList (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    (wcb_columnSorted z w).Perm (wnu_signedList z w) := by
  classical
  unfold wcb_columnSorted
  
  have hperm : ((wcb_keyedList z w).insertionSort (fun p q => p.1 ≤ q.1)).Perm
      (wcb_keyedList z w) := List.perm_insertionSort _ _
  have h1 : (((wcb_keyedList z w).insertionSort (fun p q => p.1 ≤ q.1)).map Prod.snd).Perm
      ((wcb_keyedList z w).map Prod.snd) := hperm.map _
  rw [wcb_keyedList_snd z w] at h1
  exact h1


theorem wcb_columnSorted_sum (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    (wcb_columnSorted z w).sum = wnd_signedCross z w := by
  rw [(wcb_columnOrder_permutes_signedList z w).sum_eq, wnu_signedList_sum]


theorem wcb_columnSorted_entries_pm (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    ∀ s ∈ wcb_columnSorted z w, s = 1 ∨ s = -1 := by
  classical
  intro s hs
  
  have hmem : s ∈ wnu_signedList z w :=
    (wcb_columnOrder_permutes_signedList z w).mem_iff.mp hs
  unfold wnu_signedList at hmem
  rw [List.mem_filter] at hmem
  obtain ⟨hmap, hne⟩ := hmem
  rw [List.mem_map] at hmap
  obtain ⟨d, _, hd⟩ := hmap
  
  have hmem3 := wnd_signStep_mem z d.toProd.1 d.toProd.2
  rw [hd] at hmem3
  have hne' : s ≠ 0 := by simpa using hne
  rcases hmem3 with h | h | h
  · exact Or.inl h
  · exact absurd h hne'
  · exact Or.inr h


theorem wcb_columnAlternates_of_sorted_alt (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (halt : wnu_Alt (wcb_columnSorted z w)) :
    wna_ColumnAlternates z w :=
  ⟨wcb_columnSorted z w, wcb_columnOrder_permutes_signedList z w, halt⟩


theorem wcb_unitSquare_columnSorted :
    wcb_columnSorted (![1, 1] : Site 2) wwit_unitSquareLoop = [1] := by
  have hperm := wcb_columnOrder_permutes_signedList (![1, 1] : Site 2) wwit_unitSquareLoop
  rw [wnu_unitSquare_signedList] at hperm
  
  exact hperm.eq_singleton


theorem wcb_unitSquare_columnAlternates :
    wna_ColumnAlternates (![1, 1] : Site 2) wwit_unitSquareLoop := by
  apply wcb_columnAlternates_of_sorted_alt
  rw [wcb_unitSquare_columnSorted]
  exact Or.inl rfl


theorem wcb_Ltromino_columnSorted :
    wcb_columnSorted (![1, 1] : Site 2) wnu_LtrominoLoop = [-1] := by
  have hperm := wcb_columnOrder_permutes_signedList (![1, 1] : Site 2) wnu_LtrominoLoop
  rw [wnu_Ltromino_signedList] at hperm
  exact hperm.eq_singleton


theorem wcb_Ltromino_columnAlternates :
    wna_ColumnAlternates (![1, 1] : Site 2) wnu_LtrominoLoop := by
  apply wcb_columnAlternates_of_sorted_alt
  rw [wcb_Ltromino_columnSorted]
  exact Or.inr rfl


theorem wcb_doubleSquare_columnSorted :
    wcb_columnSorted (![1, 1] : Site 2) wnu_doubleSquare = [1, 1] := by
  have hperm := wcb_columnOrder_permutes_signedList (![1, 1] : Site 2) wnu_doubleSquare
  rw [wnu_doubleSquare_signedList] at hperm
  
  have hlen := hperm.length_eq
  have hmem : ∀ s ∈ wcb_columnSorted (![1, 1] : Site 2) wnu_doubleSquare, s = 1 := by
    intro s hs
    have := hperm.mem_iff.mp hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h <;> exact h
  match wcb_columnSorted (![1, 1] : Site 2) wnu_doubleSquare, hlen, hmem with
  | [a, b], _, hmem =>
    have ha := hmem a (by simp)
    have hb := hmem b (by simp)
    rw [ha, hb]


theorem wcb_doubleSquare_not_columnSorted_alt :
    ¬ wnu_Alt (wcb_columnSorted (![1, 1] : Site 2) wnu_doubleSquare) := by
  rw [wcb_doubleSquare_columnSorted]
  exact wnu_not_alt_oneOne


end Lattice
end StatMech
