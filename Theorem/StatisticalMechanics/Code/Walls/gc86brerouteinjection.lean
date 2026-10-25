/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc86brerouteinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part3
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]


theorem gc86b_o_connects_mark (ends : ι → Sym2 W) (R : Finset ι)
    (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends R = ({o, x, y, g} : Finset W)) (ho : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    connK ends R o x ∨ connK ends R o y ∨ connK ends R o g := by
  
  have ho_odd : Odd (degK ends R o) := by
    rw [← RandomCurrent.mem_sources, hsrc]; simp
  
  have hsum_even := sum_deg_comp_even ends R hnd o
  have hcount_even : Even (#((compOf ends R o).filter (fun v => Odd (degK ends R v)))) :=
    (RandomCurrent.even_sum_iff_even_count _ _).1 hsum_even
  have ho_in : o ∈ (compOf ends R o).filter (fun v => Odd (degK ends R v)) := by
    simp only [Finset.mem_filter, RandomCurrent.mem_compOf]
    exact ⟨Relation.ReflTransGen.refl, ho_odd⟩
  
  obtain ⟨w, hw_mem, hw_ne⟩ :
      ∃ w ∈ (compOf ends R o).filter (fun v => Odd (degK ends R v)), w ≠ o := by
    by_contra hcon
    push Not at hcon
    
    have hsingle : (compOf ends R o).filter (fun v => Odd (degK ends R v)) = {o} := by
      ext v
      simp only [Finset.mem_singleton]
      constructor
      · intro hv; exact hcon v hv
      · rintro rfl; exact ho_in
    rw [hsingle, Finset.card_singleton] at hcount_even
    exact (Nat.not_even_iff_odd.2 ⟨0, rfl⟩) hcount_even
  simp only [Finset.mem_filter, RandomCurrent.mem_compOf] at hw_mem
  obtain ⟨hconn_ow, hw_odd⟩ := hw_mem
  
  have hw_bdry : w ∈ ({o, x, y, g} : Finset W) := by
    rw [← hsrc, RandomCurrent.mem_sources]; exact hw_odd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw_bdry
  rcases hw_bdry with rfl | rfl | rfl | rfl
  · exact absurd rfl hw_ne
  · exact Or.inl hconn_ow
  · exact Or.inr (Or.inl hconn_ow)
  · exact Or.inr (Or.inr hconn_ow)


end StatMech.Walls
