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
import Def.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem rlc_descend_via_leftStep {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hleft : (![x - 1, y] : Site 2) ∉ Vc.support) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : (hypercubicLattice 2).Walk (![x, y] : Site 2) z', ∀ w ∈ p.support, w ∉ Vc.support := by
  have hz' : (![x - 1, y] : Site 2) ∈ jil_offSupportInterior Vc :=
    rlc_left_mem_interior Vc hz hleft
  refine ⟨![x - 1, y], hz', ?_, ?_⟩
  · have hzL : (![x, y] : Site 2) ∈ jec_leftRegion Vc :=
      (jil_mem_offSupportInterior Vc _ |>.mp hz).2
    have hz'L : (![x - 1, y] : Site 2) ∈ jec_leftRegion Vc :=
      (jil_mem_offSupportInterior Vc _ |>.mp hz').2
    obtain ⟨⟨hb0a, hb0b⟩, ⟨hb1a, hb1b⟩⟩ := hMb _ hzL
    obtain ⟨⟨hd0a, hd0b⟩, ⟨hd1a, hd1b⟩⟩ := hMb _ hz'L
    refine rlc_lexMeasure_lt hb0a hb0b hb1a hb1b ?_ ?_ ?_ ?_ ?_
    · simpa using hd0a
    · simpa using hd0b
    · simpa using hd1a
    · simpa using hd1b
    · right; simp
  · have hadj : (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x - 1, y] := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h
    · subst h; exact (jil_mem_offSupportInterior Vc _ |>.mp hz).1
    · subst h; exact hleft


theorem rlc_descend_via_downStep {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y cx : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (preach : (hypercubicLattice 2).Walk (![x, y] : Site 2) ![cx, y])
    (hpreach : ∀ w ∈ preach.support, w ∉ Vc.support)
    (hc : (![cx, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hcdown : (![cx, y - 1] : Site 2) ∉ Vc.support) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : (hypercubicLattice 2).Walk (![x, y] : Site 2) z', ∀ w ∈ p.support, w ∉ Vc.support := by
  have hz' : (![cx, y - 1] : Site 2) ∈ jil_offSupportInterior Vc :=
    rlc_down_mem_interior Vc hc hcdown
  refine ⟨![cx, y - 1], hz', ?_, ?_⟩
  · have hzL : (![x, y] : Site 2) ∈ jec_leftRegion Vc :=
      (jil_mem_offSupportInterior Vc _ |>.mp hz).2
    have hz'L : (![cx, y - 1] : Site 2) ∈ jec_leftRegion Vc :=
      (jil_mem_offSupportInterior Vc _ |>.mp hz').2
    obtain ⟨⟨hb0a, hb0b⟩, ⟨hb1a, hb1b⟩⟩ := hMb _ hzL
    obtain ⟨⟨hd0a, hd0b⟩, ⟨hd1a, hd1b⟩⟩ := hMb _ hz'L
    refine rlc_lexMeasure_lt hb0a hb0b hb1a hb1b ?_ ?_ ?_ ?_ ?_
    · simpa using hd0a
    · simpa using hd0b
    · simpa using hd1a
    · simpa using hd1b
    · left; simp
  · have hadj : (hypercubicLattice 2).Adj (![cx, y] : Site 2) ![cx, y - 1] := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    refine ⟨preach.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hw
    rcases hw with h | h
    · exact hpreach w h
    · have hmem := List.mem_of_mem_tail h
      rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h1 | h1
      · subst h1; exact (jil_mem_offSupportInterior Vc _ |>.mp hc).1
      · subst h1; exact hcdown


theorem rlc_descend_via_segmentDown {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y cx : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hxcx : x ≤ cx)
    (hrun : ∀ t : ℤ, x ≤ t → t ≤ cx → (![t, y] : Site 2) ∉ Vc.support)
    (hcdown : (![cx, y - 1] : Site 2) ∉ Vc.support) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : (hypercubicLattice 2).Walk (![x, y] : Site 2) z', ∀ w ∈ p.support, w ∉ Vc.support := by
  have hxoff : (![x, y] : Site 2) ∉ Vc.support := (jil_mem_offSupportInterior Vc _ |>.mp hz).1
  obtain ⟨preach, hpreach⟩ :=
    jil_hsegment_reachable_offSupport {p | p ∈ Vc.support} (lo := x) (hi := cx) (y := y)
      (x₁ := x) (x₂ := cx) (by simpa using hxoff) le_rfl hxcx hxcx le_rfl
      (by intro t ht ht'; simpa using hrun t ht ht')
  have hxL : (![x, y] : Site 2) ∈ jec_leftRegion Vc := (jil_mem_offSupportInterior Vc _ |>.mp hz).2
  have hcL : (![cx, y] : Site 2) ∈ jec_leftRegion Vc :=
    jil_hsegment_subset_leftRegion Vc le_rfl hxcx hxcx le_rfl
      (by intro t ht ht'; simpa using hrun t ht ht') hxL
  have hcoff : (![cx, y] : Site 2) ∉ Vc.support := by simpa using hrun cx hxcx le_rfl
  have hc : (![cx, y] : Site 2) ∈ jil_offSupportInterior Vc :=
    (jil_mem_offSupportInterior Vc _).mpr ⟨hcoff, hcL⟩
  have hpreach' : ∀ w ∈ preach.support, w ∉ Vc.support := by
    intro w hw; have := hpreach w hw; simpa using this
  exact rlc_descend_via_downStep Vc M hMb hz preach hpreach' hc hcdown


end Lattice
end StatMech
