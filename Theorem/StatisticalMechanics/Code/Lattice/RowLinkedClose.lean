/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem rlc_rayCount_zero_left (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : ∀ p ∈ w.support, z 0 ≤ p 0) :
    jec_rayCount z w = 0 :=
  jec_rayCount_eq_zero_of_right z w h


theorem rlc_rayCount_zero_below (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : ∀ p ∈ w.support, z 1 ≤ p 1) :
    jec_rayCount z w = 0 := by
  classical
  rw [jec_rayCount, List.countP_eq_zero]
  intro e he; obtain ⟨u, v⟩ := e
  have hu := h u (w.fst_mem_support_of_mem_edges he)
  have hv := h v (w.snd_mem_support_of_mem_edges he)
  simp only [decide_eq_true_eq]; rw [jec_rayEdge_mk]; omega


theorem rlc_rayCount_zero_above (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : ∀ p ∈ w.support, p 1 ≤ z 1 - 1) :
    jec_rayCount z w = 0 := by
  classical
  rw [jec_rayCount, List.countP_eq_zero]
  intro e he; obtain ⟨u, v⟩ := e
  have hu := h u (w.fst_mem_support_of_mem_edges he)
  have hv := h v (w.snd_mem_support_of_mem_edges he)
  simp only [decide_eq_true_eq]; rw [jec_rayEdge_mk]; omega


theorem rlc_support_bound {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    ∃ M : ℤ, ∀ p ∈ Vc.support, |p 0| ≤ M ∧ |p 1| ≤ M := by
  classical
  refine ⟨((Vc.support.map (fun p => max (p 0).natAbs (p 1).natAbs)).foldr max 0 : ℕ), ?_⟩
  intro p hp
  set N : ℕ := (Vc.support.map (fun p => max (p 0).natAbs (p 1).natAbs)).foldr max 0 with hN
  have hmem : max (p 0).natAbs (p 1).natAbs ∈
      Vc.support.map (fun p => max (p 0).natAbs (p 1).natAbs) := List.mem_map_of_mem hp
  have hle : max (p 0).natAbs (p 1).natAbs ≤ N := by
    rw [hN]; exact List.le_max_of_le hmem (le_refl _)
  have h0 : (p 0).natAbs ≤ N := le_trans (le_max_left _ _) hle
  have h1 : (p 1).natAbs ≤ N := le_trans (le_max_right _ _) hle
  refine ⟨?_, ?_⟩
  · rw [Int.abs_eq_natAbs]; exact_mod_cast h0
  · rw [Int.abs_eq_natAbs]; exact_mod_cast h1


theorem rlc_interior_bounded {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    ∃ M : ℤ, ∀ z ∈ jec_leftRegion Vc,
      (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M) := by
  obtain ⟨M, hM⟩ := rlc_support_bound Vc
  refine ⟨M + 1, ?_⟩
  intro z hz
  rw [jec_mem_leftRegion] at hz
  
  have hcol : ∀ p ∈ Vc.support, -M ≤ p 0 ∧ p 0 ≤ M := by
    intro p hp; have := (hM p hp).1; rw [abs_le] at this; exact this
  have hrow : ∀ p ∈ Vc.support, -M ≤ p 1 ∧ p 1 ≤ M := by
    intro p hp; have := (hM p hp).2; rw [abs_le] at this; exact this
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · 
    by_contra hcon
    push Not at hcon
    exact hz (by
      rw [rlc_rayCount_zero_left z Vc (fun p hp => by have := (hcol p hp).1; omega)]
      exact ⟨0, rfl⟩)
  · 
    by_contra hcon
    push Not at hcon
    exact hz (jec_ray_even_far Vc z (fun p hp => by have := (hcol p hp).2; omega))
  · 
    by_contra hcon
    push Not at hcon
    exact hz (by
      rw [rlc_rayCount_zero_below z Vc (fun p hp => by have := (hrow p hp).1; omega)]
      exact ⟨0, rfl⟩)
  · 
    by_contra hcon
    push Not at hcon
    exact hz (by
      rw [rlc_rayCount_zero_above z Vc (fun p hp => by have := (hrow p hp).2; omega)]
      exact ⟨0, rfl⟩)


theorem rlc_offSupportInterior_finite {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    (jil_offSupportInterior Vc).Finite := by
  obtain ⟨M, hM⟩ := rlc_interior_bounded Vc
  apply Set.Finite.subset
    (Set.Finite.pi (fun _ : Fin 2 => Set.finite_Icc (-(M : ℤ) - 1) (M : ℤ)))
  intro z hz
  have hzL : z ∈ jec_leftRegion Vc := (jil_mem_offSupportInterior Vc z |>.mp hz).2
  obtain ⟨⟨h0a, h0b⟩, ⟨h1a, h1b⟩⟩ := hM z hzL
  intro i _
  rw [Set.mem_Icc]
  fin_cases i <;> simp <;> constructor <;> omega


end Lattice
end StatMech
