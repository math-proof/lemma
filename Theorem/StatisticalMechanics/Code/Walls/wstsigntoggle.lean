/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean -/

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
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

theorem wst_prefixSum_telescope (ind : ℕ → ℤ) :
    ∀ n : ℕ, ((List.range n).map (fun i => ind (i + 1) - ind i)).sum = ind n - ind 0 := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring


theorem wst_prefixSums_in_01_of_indicatorSteps (ind : ℕ → ℤ)
    (h01 : ∀ n, ind n = 0 ∨ ind n = 1) (h0 : ind 0 = 0) (n : ℕ) :
    ∀ p ∈ wna_prefixSums ((List.range n).map (fun i => ind (i + 1) - ind i)),
      p = 0 ∨ p = 1 := by
  intro p hp
  
  
  
  
  obtain ⟨k, hk, hpk⟩ : ∃ k, k ≤ n ∧
      p = ((List.range k).map (fun i => ind (i + 1) - ind i)).sum := by
    
    unfold wna_prefixSums at hp
    have hmem := List.mem_of_mem_tail hp
    
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨j, hj, hjeq⟩ := hmem
    
    have hjlt : j ≤ n := by
      rw [List.length_scanl, List.length_map, List.length_range] at hj; omega
    refine ⟨j, hjlt, ?_⟩
    rw [← hjeq, List.getElem_scanl]
    
    have htake : ((List.range n).map (fun i => ind (i + 1) - ind i)).take j
        = (List.range j).map (fun i => ind (i + 1) - ind i) := by
      rw [← List.map_take, List.take_range, min_eq_left hjlt]
    rw [htake, ← List.sum_eq_foldl]
  rw [hpk, wst_prefixSum_telescope ind k, h0, sub_zero]
  exact h01 k


theorem wst_prefixSums_in_01_of_toggle (L : List ℤ) (ind : ℕ → ℤ)
    (h01 : ∀ n, ind n = 0 ∨ ind n = 1) (h0 : ind 0 = 0)
    (hL : L = (List.range L.length).map (fun i => ind (i + 1) - ind i)) :
    ∀ p ∈ wna_prefixSums L, p = 0 ∨ p = 1 := by
  intro p hp
  rw [hL] at hp
  exact wst_prefixSums_in_01_of_indicatorSteps ind h01 h0 L.length p hp


theorem wst_alt_of_indicatorSteps (L : List ℤ) (ind : ℕ → ℤ)
    (hpm : ∀ x ∈ L, x = 1 ∨ x = -1)
    (h01 : ∀ n, ind n = 0 ∨ ind n = 1) (h0 : ind 0 = 0)
    (hL : L = (List.range L.length).map (fun i => ind (i + 1) - ind i)) :
    wnu_Alt L :=
  wna_alt_of_prefixSums_in_01 L hpm (wst_prefixSums_in_01_of_toggle L ind h01 h0 hL)


theorem wst_alt_map_neg : ∀ L : List ℤ, wnu_Alt L → wnu_Alt (L.map (fun x => -x))
  | [], _ => trivial
  | [a], h => by simp only [List.map_cons, List.map_nil]; rcases h with h | h <;> simp [h]
  | a :: b :: t, h => by
      obtain ⟨ha, hb, ht⟩ := wnu_Alt_cons_cons.mp h
      have htail : wnu_Alt ((b :: t).map (fun x => -x)) := wst_alt_map_neg (b :: t) ht
      simp only [List.map_cons] at htail ⊢
      refine ⟨?_, ?_, htail⟩
      · rcases ha with h | h <;> simp [h]
      · subst hb; ring


theorem wst_alt_of_prefixSums_in_0neg (L : List ℤ)
    (hpm : ∀ x ∈ L, x = 1 ∨ x = -1)
    (hpref : ∀ p ∈ wna_prefixSums L, p = 0 ∨ p = -1) :
    wnu_Alt L := by
  
  set Lneg := L.map (fun x => -x) with hLneg
  have hpmneg : ∀ x ∈ Lneg, x = 1 ∨ x = -1 := by
    intro x hx
    rw [hLneg, List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rcases hpm a ha with h | h <;> simp [h]
  
  have hprefneg_eq : wna_prefixSums Lneg = (wna_prefixSums L).map (fun x => -x) := by
    unfold wna_prefixSums
    rw [hLneg]
    
    have hscan : ∀ (s : ℤ) (M : List ℤ),
        (M.map (fun x => -x)).scanl (· + ·) (-s) = (M.scanl (· + ·) s).map (fun x => -x) := by
      intro s M
      induction M generalizing s with
      | nil => simp
      | cons a t ih =>
        rw [List.map_cons, List.scanl_cons, List.scanl_cons, List.map_cons]
        congr 1
        rw [show -s + -a = -(s + a) from by ring, ih (s + a)]
    have := hscan 0 L
    simp only [neg_zero] at this
    rw [this, ← List.map_tail]
  have hprefneg : ∀ p ∈ wna_prefixSums Lneg, p = 0 ∨ p = 1 := by
    intro p hp
    rw [hprefneg_eq, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rcases hpref q hq with h | h <;> simp [h]
  have haltneg : wnu_Alt Lneg := wna_alt_of_prefixSums_in_01 Lneg hpmneg hprefneg
  
  have hLL : L = Lneg.map (fun x => -x) := by
    rw [hLneg, List.map_map]; simp
  rw [hLL]
  exact wst_alt_map_neg Lneg haltneg


theorem wst_alt_of_indicatorSteps_neg (L : List ℤ) (ind : ℕ → ℤ)
    (hpm : ∀ x ∈ L, x = 1 ∨ x = -1)
    (h0neg : ∀ n, ind n = 0 ∨ ind n = -1) (h0 : ind 0 = 0)
    (hL : L = (List.range L.length).map (fun i => ind (i + 1) - ind i)) :
    wnu_Alt L := by
  apply wst_alt_of_prefixSums_in_0neg L hpm
  intro p hp
  
  obtain ⟨k, hpk⟩ : ∃ k, p = ind k := by
    unfold wna_prefixSums at hp
    have hmem := List.mem_of_mem_tail hp
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨j, hj, hjeq⟩ := hmem
    have hjlt : j ≤ L.length := by
      rw [List.length_scanl] at hj; omega
    refine ⟨j, ?_⟩
    rw [← hjeq, List.getElem_scanl]
    
    have htake : L.take j = (List.range j).map (fun i => ind (i + 1) - ind i) := by
      conv_lhs => rw [hL]
      rw [← List.map_take, List.take_range, min_eq_left hjlt]
    rw [htake, ← List.sum_eq_foldl, wst_prefixSum_telescope ind j, h0, sub_zero]
  rw [hpk]; exact h0neg k


end Lattice
end StatMech
