/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc5_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.kc4_core.Part2
import Def.StatisticalMechanics.Code.Walls.kc5_core
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc5_offSupportInfinite_of_outsideInfinite (Vc : (hypercubicLattice 2).Walk a a)
    (h : kc4_OutsideInInfiniteComponent Vc) : kc5_OutsideOffSupportInfinite Vc :=
  fun z _ hzout => h z hzout


theorem kc5_outsideInfinite_forces_supportOdd (Vc : (hypercubicLattice 2).Walk a a)
    (h : kc4_OutsideInInfiniteComponent Vc) :
    ∀ z ∈ Vc.support, ¬ Even (jec_rayCount z Vc) := by
  intro z hz hev
  have hzout : z ∉ jec_leftRegion Vc := by
    rw [jec_mem_leftRegion]; exact not_not.mpr hev
  obtain ⟨hzmem, _⟩ := h z hzout
  simp only [Set.mem_compl_iff, oc_mem_supportSet] at hzmem
  exact hzmem hz


theorem kc5_outsideInfinite_iff_offSupport_and_supportOdd (Vc : (hypercubicLattice 2).Walk a a) :
    kc4_OutsideInInfiniteComponent Vc ↔
      (kc5_OutsideOffSupportInfinite Vc ∧ ∀ z ∈ Vc.support, ¬ Even (jec_rayCount z Vc)) := by
  constructor
  · intro h
    exact ⟨kc5_offSupportInfinite_of_outsideInfinite Vc h,
           kc5_outsideInfinite_forces_supportOdd Vc h⟩
  · rintro ⟨hoff, hpar⟩ z hzout
    have heven : Even (jec_rayCount z Vc) := by
      rw [jec_mem_leftRegion] at hzout; exact not_not.mp hzout
    have hzoff : z ∉ Vc.support := fun hzs => hpar z hzs heven
    exact hoff z hzoff hzout


end Walls
end StatMech
