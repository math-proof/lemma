/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoPinchMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Def.StatisticalMechanics.Code.Lattice.NoPinchMatching
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem npm_noDiagTouch_of_kingSaturated {K : Set (Site 2)} (h : npm_KingSaturated K) :
    npd_NoDiagTouch K := by
  intro f hf
  rcases hf with ⟨h00, h11, h10, h01⟩ | ⟨h10, h01, h00, h11⟩
  · rcases (h f).1 h00 h11 with h | h
    · exact h10 h
    · exact h01 h
  · rcases (h f).2 h10 h01 with h | h
    · exact h00 h
    · exact h11 h


theorem npm_kingSaturated_diagTouch_iff (K : Set (Site 2)) :
    npm_KingSaturated K ↔ npd_NoDiagTouch K := by
  constructor
  · exact npm_noDiagTouch_of_kingSaturated
  · intro h f
    refine ⟨?_, ?_⟩
    · intro h00 h11
      by_contra hcon
      rw [not_or] at hcon
      exact h f (Or.inl ⟨h00, h11, hcon.1, hcon.2⟩)
    · intro h10 h01
      by_contra hcon
      rw [not_or] at hcon
      exact h f (Or.inr ⟨h10, h01, hcon.1, hcon.2⟩)


theorem npm_orbitFaceNoPinch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : npm_KingSaturated K) :
    OrbitFaceNoPinch K a :=
  npd_orbitFaceNoPinch_of_globalNoDiagTouch K a (npm_noDiagTouch_of_kingSaturated h)


theorem npm_orbitFace_injOn (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : npm_KingSaturated K) :
    Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) :=
  orbitFace_injOn_of_noPinch K a (npm_orbitFaceNoPinch K a h)


theorem npm_diagTouch_not_kingSaturated {K : Set (Site 2)} {f : Site 2}
    (h : npd_DiagTouch K f) : ¬ npm_KingSaturated K := by
  intro hsat
  exact npm_noDiagTouch_of_kingSaturated hsat f h


theorem npm_kingSaturated_example :
    npm_KingSaturated ({![0, 0], ![1, 0], ![0, 1], ![1, 1]} : Set (Site 2)) := by
  
  
  rw [npm_kingSaturated_diagTouch_iff]
  intro f hf
  
  
  have corner_coords : ∀ p : Site 2, p ∈ ({![0, 0], ![1, 0], ![0, 1], ![1, 1]} : Set (Site 2)) →
      (p 0 = 0 ∨ p 0 = 1) ∧ (p 1 = 0 ∨ p 1 = 1) := by
    intro p hp
    rcases hp with hp | hp | hp | hp <;>
      refine ⟨?_, ?_⟩ <;> rw [hp] <;> simp
  rcases hf with ⟨h00, h11, h10, h01⟩ | ⟨h10, h01, h00, h11⟩
  · 
    
    
    obtain ⟨c00_0, c00_1⟩ := corner_coords _ h00
    obtain ⟨c11_0, c11_1⟩ := corner_coords _ h11
    simp only [npd_P00, npd_P11, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at c00_0 c00_1 c11_0 c11_1
    have hf0 : f 0 = 0 := by omega
    have hf1 : f 1 = 0 := by omega
    apply h10
    show npd_P10 f ∈ ({![0, 0], ![1, 0], ![0, 1], ![1, 1]} : Set (Site 2))
    right; left
    funext i; fin_cases i <;> simp [npd_P10, hf0, hf1]
  · 
    
    
    obtain ⟨c10_0, c10_1⟩ := corner_coords _ h10
    obtain ⟨c01_0, c01_1⟩ := corner_coords _ h01
    simp only [npd_P10, npd_P01, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at c10_0 c10_1 c01_0 c01_1
    have hf0 : f 0 = 0 := by omega
    have hf1 : f 1 = 0 := by omega
    apply h00
    show npd_P00 f ∈ ({![0, 0], ![1, 0], ![0, 1], ![1, 1]} : Set (Site 2))
    left
    funext i; fin_cases i <;> simp [npd_P00, hf0, hf1]


end Lattice
end StatMech
