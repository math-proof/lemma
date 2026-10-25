/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.umffullrev.Part2
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
import Theorem.StatisticalMechanics.Code.Walls.wcbcolumnbridge.Part4
import Theorem.StatisticalMechanics.Code.Walls.wstsigntoggle.Part2
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
import Def.StatisticalMechanics.Code.Walls.wisindicatorsteps.Part2
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


theorem wis_take_filter {α : Type*} (p : α → Bool) (L : List α) (k : ℕ) :
    ∃ j ≤ L.length, (L.filter p).take k = (L.take j).filter p := by
  induction L generalizing k with
  | nil => exact ⟨0, le_refl 0, by simp⟩
  | cons a t ih =>
    by_cases hp : p a
    · cases k with
      | zero => exact ⟨0, by simp, by simp⟩
      | succ k' =>
        obtain ⟨j, hj, hje⟩ := ih k'
        refine ⟨j + 1, by simpa using hj, ?_⟩
        rw [List.filter_cons_of_pos hp, List.take_succ_cons, List.take_succ_cons,
          List.filter_cons_of_pos hp, hje]
    · obtain ⟨j, hj, hje⟩ := ih k
      refine ⟨j + 1, by simpa using hj, ?_⟩
      rw [List.filter_cons_of_neg hp, List.take_succ_cons, List.filter_cons_of_neg hp, hje]


theorem wis_take_nonzeroDiffs (f : ℕ → ℤ) (n k : ℕ) :
    ∃ m ≤ n, (wis_nonzeroDiffs f n).take k = wis_nonzeroDiffs f m := by
  unfold wis_nonzeroDiffs
  obtain ⟨j, hj, hje⟩ := wis_take_filter (fun d => decide (d ≠ 0))
    ((List.range n).map (fun i => f (i + 1) - f i)) k
  rw [List.length_map, List.length_range] at hj
  refine ⟨j, hj, ?_⟩
  rw [hje, ← List.map_take, List.take_range, min_eq_left hj]


theorem wis_nonzeroDiffs_sum (f : ℕ → ℤ) (h0 : f 0 = 0) (n : ℕ) :
    (wis_nonzeroDiffs f n).sum = f n := by
  unfold wis_nonzeroDiffs
  induction n with
  | zero => simp [h0]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.filter_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil]
    by_cases hd : f (k + 1) - f k = 0
    · rw [List.filter_cons_of_neg (by simp [hd]), List.filter_nil]
      simp only [List.sum_nil, add_zero]; omega
    · rw [List.filter_cons_of_pos (by simp [hd]), List.filter_nil]
      simp only [List.sum_cons, List.sum_nil, add_zero]; ring


theorem wis_nonzeroDiffs_isIndicatorStep (f : ℕ → ℤ)
    (h01 : ∀ n, f n = 0 ∨ f n = 1) (h0 : f 0 = 0) (n : ℕ) :
    ∃ ind : ℕ → ℤ,
      (∀ e ∈ wis_nonzeroDiffs f n, e = 1 ∨ e = -1) ∧ ind 0 = 0 ∧
      (∀ m, ind m = 0 ∨ ind m = 1) ∧
      wis_nonzeroDiffs f n =
        (List.range (wis_nonzeroDiffs f n).length).map (fun i => ind (i + 1) - ind i) := by
  set D := wis_nonzeroDiffs f n with hD
  
  have hpm : ∀ e ∈ D, e = 1 ∨ e = -1 := by
    intro e he
    rw [hD, wis_nonzeroDiffs, List.mem_filter] at he
    obtain ⟨hmem, hne⟩ := he
    rw [List.mem_map] at hmem
    obtain ⟨i, _, rfl⟩ := hmem
    have := h01 (i + 1); have := h01 i
    simp only [ne_eq, decide_eq_true_eq] at hne
    omega
  
  
  
  refine ⟨fun k => (D.take k).sum, hpm, by simp, ?_, ?_⟩
  · 
    
    intro k
    
    
    
    
    
    have hprefix : ∃ m ≤ n, D.take k = wis_nonzeroDiffs f m := by
      rcases Nat.lt_or_ge k D.length with hlt | hge
      · 
        
        
        exact wis_take_nonzeroDiffs f n k
      · exact ⟨n, le_refl n, by rw [List.take_of_length_le hge]⟩
    obtain ⟨m, _, hm⟩ := hprefix
    show (D.take k).sum = 0 ∨ (D.take k).sum = 1
    rw [hm, wis_nonzeroDiffs_sum f h0 m]
    exact h01 m
  · 
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      rw [List.length_map, List.length_range] at h2
      simp only [List.getElem_map, List.getElem_range]
      show D[i] = (D.take (i + 1)).sum - (D.take i).sum
      have hkey : (D.take (i + 1)).sum - (D.take i).sum = D[i] := by
        rw [List.take_add_one, List.sum_append, List.getElem?_eq_getElem h2]
        simp
      omega


end Lattice
end StatMech
