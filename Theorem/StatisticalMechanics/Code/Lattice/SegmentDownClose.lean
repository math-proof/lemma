/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part5
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem sdc_down_on_support_of_notInterior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : ℤ} (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hnot : (![x, y - 1] : Site 2) ∉ jil_offSupportInterior Vc) :
    (![x, y - 1] : Site 2) ∈ Vc.support := by
  obtain ⟨hzsup, hzint⟩ := (jil_mem_offSupportInterior Vc _).mp hz
  by_contra hdown
  
  have hadj : (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x, y - 1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  have hpar := jec_localConstancy Vc hadj hzsup hdown
  refine hnot ?_
  rw [jil_mem_offSupportInterior]
  refine ⟨hdown, ?_⟩
  rw [jec_mem_leftRegion] at hzint ⊢
  intro h; exact hzint (hpar.mpr h)


theorem sdc_no_segmentDown_of_bottomInterior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : ℤ} (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hbot : ∀ t : ℤ, (![t, y - 1] : Site 2) ∉ jil_offSupportInterior Vc) :
    ¬ ∃ cx : ℤ, x ≤ cx ∧
        (∀ t : ℤ, x ≤ t → t ≤ cx → (![t, y] : Site 2) ∉ Vc.support) ∧
        (![cx, y - 1] : Site 2) ∉ Vc.support := by
  rintro ⟨cx, hxcx, hrun, hcdown⟩
  
  
  have hcoff : (![cx, y] : Site 2) ∉ Vc.support := hrun cx hxcx le_rfl
  have hcL : (![cx, y] : Site 2) ∈ jec_leftRegion Vc :=
    jil_hsegment_subset_leftRegion Vc (lo := x) (hi := cx) (y := y)
      (x₀ := x) (x := cx) le_rfl hxcx hxcx le_rfl
      (by intro t ht ht'; exact hrun t ht ht')
      (jil_mem_offSupportInterior Vc _ |>.mp hz).2
  have hc : (![cx, y] : Site 2) ∈ jil_offSupportInterior Vc :=
    (jil_mem_offSupportInterior Vc _).mpr ⟨hcoff, hcL⟩
  exact hcdown (sdc_down_on_support_of_notInterior Vc hc (by simpa using hbot cx))


end Lattice
end StatMech
