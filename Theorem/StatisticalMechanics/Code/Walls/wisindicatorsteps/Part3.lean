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
import Def.StatisticalMechanics.Code.Walls.wisindicatorsteps.Part3
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


theorem wis_indSeq_in_01 (z : Site 2) {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (c₀ : ℤ) (i : ℕ) : wis_indSeq z Vc c₀ i = 0 ∨ wis_indSeq z Vc c₀ i = 1 :=
  wis_ind_in_01 z Vc _


theorem wis_nonzeroDiffs_neg_isIndicatorStep (f : ℕ → ℤ)
    (h01 : ∀ n, f n = 0 ∨ f n = 1) (h0 : f 0 = 0) (n : ℕ) :
    ∃ ind : ℕ → ℤ,
      (∀ e ∈ wis_nonzeroDiffs (fun i => - f i) n, e = 1 ∨ e = -1) ∧ ind 0 = 0 ∧
      (∀ m, ind m = 0 ∨ ind m = -1) ∧
      wis_nonzeroDiffs (fun i => - f i) n =
        (List.range (wis_nonzeroDiffs (fun i => - f i) n).length).map
          (fun i => ind (i + 1) - ind i) := by
  have h01' : ∀ m, (fun i => - f i) m = 0 ∨ (fun i => - f i) m = -1 := by
    intro m; rcases h01 m with h | h <;> simp [h]
  have h0' : (fun i => - f i) 0 = 0 := by simp [h0]
  
  
  set D := wis_nonzeroDiffs (fun i => - f i) n with hD
  have hpm : ∀ e ∈ D, e = 1 ∨ e = -1 := by
    intro e he
    rw [hD, wis_nonzeroDiffs, List.mem_filter] at he
    obtain ⟨hmem, hne⟩ := he
    rw [List.mem_map] at hmem
    obtain ⟨i, _, rfl⟩ := hmem
    have := h01 (i + 1); have := h01 i
    simp only [ne_eq, decide_eq_true_eq] at hne ⊢
    omega
  refine ⟨fun k => (D.take k).sum, hpm, by simp, ?_, ?_⟩
  · intro k
    have hprefix : ∃ m ≤ n, D.take k = wis_nonzeroDiffs (fun i => - f i) m := by
      rcases Nat.lt_or_ge k D.length with _ | hge
      · exact wis_take_nonzeroDiffs (fun i => - f i) n k
      · exact ⟨n, le_refl n, by rw [List.take_of_length_le hge]⟩
    obtain ⟨m, _, hm⟩ := hprefix
    show (D.take k).sum = 0 ∨ (D.take k).sum = -1
    rw [hm, wis_nonzeroDiffs_sum (fun i => - f i) h0' m]
    rcases h01 m with h | h <;> simp [h]
  · apply List.ext_getElem
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
