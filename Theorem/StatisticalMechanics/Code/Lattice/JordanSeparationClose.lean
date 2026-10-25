/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem jsc_walk_col_bound {a b : Site 2} (Vc : (hypercubicLattice 2).Walk a b) :
    ∃ M : ℤ, ∀ p ∈ Vc.support, p 0 ≤ M := by
  classical
  refine ⟨(Vc.support.map (fun p => p 0)).foldr max 0, ?_⟩
  intro p hp
  have hmem : p 0 ∈ Vc.support.map (fun p => p 0) := List.mem_map_of_mem hp
  
  have hkey : ∀ (l : List ℤ) (x : ℤ), x ∈ l → x ≤ l.foldr max 0 := by
    intro l
    induction l with
    | nil => intro x hx; exact absurd hx (List.not_mem_nil)
    | cons c t ih =>
      intro x hx
      rw [List.foldr_cons]
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact le_max_left _ _
      · exact le_trans (ih x hx) (le_max_right _ _)
  exact hkey _ _ hmem


theorem jsc_exists_outside {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    ∃ q : Site 2, q ∉ jec_leftRegion Vc ∧ ∀ p ∈ Vc.support, p 0 ≤ q 0 - 1 := by
  obtain ⟨M, hM⟩ := jsc_walk_col_bound Vc
  refine ⟨![M + 1, 0], ?_, ?_⟩
  · rw [jec_mem_leftRegion, not_not]
    refine jec_ray_even_far Vc ![M + 1, 0] ?_
    intro p hp
    have := hM p hp
    simp only [Matrix.cons_val_zero]; omega
  · intro p hp
    have := hM p hp
    simp only [Matrix.cons_val_zero]; omega


theorem jsc_inside_not_reachable_outside {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hx : ¬ Even (jec_rayCount x Vc)) (hy : Even (jec_rayCount y Vc)) :
    ¬ (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y :=
  not_reachable_latticeMinusBarrier (jec_leftRegion Vc)
    (by rw [jec_mem_leftRegion]; exact hx)
    (by rw [jec_mem_leftRegion, not_not]; exact hy)


theorem jsc_side_constant {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : Site 2}
    (h : (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y) :
    (Even (jec_rayCount x Vc) ↔ Even (jec_rayCount y Vc)) := by
  have hb := barrier_sameSide_of_reachable (jec_leftRegion Vc) h
  simp only [jec_mem_leftRegion] at hb
  exact not_iff_not.mp hb


theorem jsc_two_components_of_connected {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {p : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
  obtain ⟨q, _hq, hqfar⟩ := jsc_exists_outside Vc
  exact ccs_closedLoop_two_components Vc hp hqfar hin hout


end Lattice
end StatMech
