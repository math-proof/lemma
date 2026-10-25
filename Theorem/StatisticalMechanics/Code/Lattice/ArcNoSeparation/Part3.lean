/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.FiniteComplementConnected
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Def.StatisticalMechanics.Code.Lattice.ArcNoSeparation.Part3
open Set SimpleGraph


namespace StatMech

namespace Lattice

theorem arcns_vlshape_support (x0 y0 x1 y1 : ℤ) (z : Site 2) :
    z ∈ (arcns_vlshape x0 y0 x1 y1).support
      ↔ (∃ t : ℤ, t ∈ Set.uIcc y0 y1 ∧ z = ![x0, t])
        ∨ (∃ t : ℤ, t ∈ Set.uIcc x0 x1 ∧ z = ![t, y1]) := by
  unfold arcns_vlshape
  rw [Walk.mem_support_append_iff, sw_vertSeg_mem_support, sw_horizSeg_mem_support]


theorem arcns_reachesFarLeft_singlePoint (u : Site 2) :
    arcns_ReachesFarLeft ({u} : Set (Site 2)) := by
  classical
  refine ⟨u 0, by intro q hq; rw [Set.mem_singleton_iff] at hq; subst hq; rfl, ?_⟩
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  
  set r : ℤ := if x 1 = u 1 then x 1 + 1 else x 1 with hr
  set M : ℤ := min (x 0) (u 0) - 1 with hM
  have hru : r ≠ u 1 := by rw [hr]; split_ifs with h <;> omega
  have hx0ne : x 1 = u 1 → x 0 ≠ u 0 := by
    intro h hc; exact hx (by funext i; fin_cases i <;> simp_all)
  have estart : (![x 0, x 1] : Site 2) = x := by funext i; fin_cases i <;> rfl
  refine ⟨![M, r], (arcns_vlshape (x 0) (x 1) M r).copy estart rfl, ?_, by
    simp only [Matrix.cons_val_zero]; omega⟩
  intro w hw hwu
  rw [Set.mem_singleton_iff] at hwu
  rw [Walk.support_copy, arcns_vlshape_support] at hw
  rcases hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · 
    have hw0 : x 0 = u 0 := by have := congrFun hwu 0; simpa using this
    have hw1 : t = u 1 := by have := congrFun hwu 1; simpa using this
    by_cases hc : x 1 = u 1
    · exact hx0ne hc hw0
    · rw [hr, if_neg hc, Set.uIcc_self, Set.mem_singleton_iff] at ht
      exact hc (by rw [← ht, hw1])
  · 
    have hw1 : r = u 1 := by have := congrFun hwu 1; simpa using this
    exact hru hw1


theorem arcns_singlePoint_connected (u : Site 2) :
    arcns_OffSupportConnected ({u} : Set (Site 2)) :=
  arcns_connected_of_reachesFarLeft (arcns_reachesFarLeft_singlePoint u)


end Lattice
end StatMech
