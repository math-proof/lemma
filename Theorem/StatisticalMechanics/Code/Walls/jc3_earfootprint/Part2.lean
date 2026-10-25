/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
import Theorem.StatisticalMechanics.Code.Walls.jc_steplocal
import Theorem.StatisticalMechanics.Code.Walls.jc2_runframe.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc2_thickshelf.Part3
import Def.StatisticalMechanics.Code.Walls.jc3_earfootprint.Part2
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc3_notProbed_of_avoidsEarFootprint (r : Site 2) (e : Dart)
    (h : jc3_AvoidsEarFootprint r e) : bpc_NotProbed r e := by
  obtain ⟨hhead, htail⟩ := h
  refine ⟨?_, ?_⟩
  · 
    intro heq
    apply hhead
    rw [jc_headTravel_eq] at *
    rw [heq]
    exact jc3_self_mem_earFootprint r
  · intro heq
    apply htail
    rw [jc_tailTravel_eq] at *
    rw [heq]
    exact jc3_self_mem_earFootprint r


theorem jc3_dartNext_eq_of_avoidsEarFootprint (K : Set (Site 2)) (r : Site 2) (e : Dart)
    (h : jc3_AvoidsEarFootprint r e) :
    dartNext (K \ {r}) e = dartNext K e :=
  bpc_dartNext_diff_singleton K r e (jc3_notProbed_of_avoidsEarFootprint r e h)


theorem jc3_turnZ_eq_of_avoidsEarFootprint (K : Set (Site 2)) (r : Site 2) (e : Dart)
    (h : jc3_AvoidsEarFootprint r e) :
    turnZ (K \ {r}) e = turnZ K e :=
  bpc_turnZ_diff_singleton K r e (jc3_notProbed_of_avoidsEarFootprint r e h)


theorem jc3_step_eq_of_avoidsEarFootprint (K : Set (Site 2)) (r : Site 2) (e : Dart)
    (h : jc3_AvoidsEarFootprint r e) :
    dartNext (K \ {r}) e = dartNext K e ∧ turnZ (K \ {r}) e = turnZ K e :=
  ⟨jc3_dartNext_eq_of_avoidsEarFootprint K r e h,
   jc3_turnZ_eq_of_avoidsEarFootprint K r e h⟩


theorem jc3_earFootprintLocality (K : Set (Site 2)) (r : Site 2) (e : Dart)
    (h : jc3_AvoidsEarFootprint r e) :
    dartNext (K \ {r}) e = dartNext K e ∧ turnZ (K \ {r}) e = turnZ K e ∧
      turn (K \ {r}) e = turn K e := by
  
  obtain ⟨hnp1, hnp2⟩ := jc3_notProbed_of_avoidsEarFootprint r e h
  refine jc_step_local (K \ {r}) K e ?_ ?_
  · constructor
    · intro hmem; exact (Set.mem_diff _).mp hmem |>.1
    · intro hmem
      refine (Set.mem_diff _).mpr ⟨hmem, ?_⟩
      simp only [Set.mem_singleton_iff]
      exact hnp1
  · constructor
    · intro hmem; exact (Set.mem_diff _).mp hmem |>.1
    · intro hmem
      refine (Set.mem_diff _).mpr ⟨hmem, ?_⟩
      simp only [Set.mem_singleton_iff]
      exact hnp2


theorem jc3_mem_diff_singleton_of_ne (K : Set (Site 2)) (r x : Site 2) (hx : x ≠ r) :
    x ∈ K \ {r} ↔ x ∈ K := by
  rw [Set.mem_diff, Set.mem_singleton_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩


theorem jc3_symmDiff_diff_singleton_subset (K : Set (Site 2)) (r : Site 2) :
    (K \ (K \ {r})) ∪ ((K \ {r}) \ K) ⊆ {r} := by
  intro x hx
  rcases hx with hx | hx
  · 
    obtain ⟨hxK, hxnd⟩ := hx
    simp only [Set.mem_diff, Set.mem_singleton_iff, not_and, not_not] at hxnd
    exact hxnd hxK
  · 
    obtain ⟨hxd, hxK⟩ := hx
    exact absurd hxd.1 hxK


end Walls
end StatMech
