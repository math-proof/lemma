/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InteriorWindingClose
import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior.Part6
import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part5
import Def.StatisticalMechanics.Code.Lattice.KingInteriorFloodClose.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem kif_kingDownLink_of_kingSegmentDown {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ)
    (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    (hres : kif_KingSegmentDown Vc seed) :
    kif_KingDownLink Vc seed M := by
  intro z hz hzs
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  by_cases hleft : (![z 0 - 1, z 1] : Site 2) ∈ Vc.support
  · 
    obtain ⟨cx, hxcx, hrun, hdesc⟩ := hres z hz hzs hleft
    rw [hzeq] at hz ⊢
    rcases hdesc with hdown | ⟨helbow, hdiag⟩
    · exact kif_descend_via_segmentDown Vc M hMb (x := z 0) (y := z 1) (cx := cx) hz
        (by simpa using hxcx)
        (by intro t ht ht'; have := hrun t (by simpa using ht) ht'; simpa using this)
        (by simpa using hdown)
    · exact kif_descend_via_segmentDiagDR Vc M hMb (x := z 0) (y := z 1) (cx := cx) hz
        (by simpa using hxcx)
        (by intro t ht ht'; have := hrun t (by simpa using ht) ht'; simpa using this)
        (by simpa using helbow) (by simpa using hdiag)
  · 
    rw [hzeq] at hz hleft ⊢
    have hl : (![(![z 0, z 1] : Site 2) 0 - 1, (![z 0, z 1] : Site 2) 1] : Site 2)
        ∉ Vc.support := by simpa using hleft
    exact kif_descend_via_leftStep Vc M hMb hz hl


theorem kif_kingRowLinked_of_kingSegmentDown {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ)
    (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    (hres : kif_KingSegmentDown Vc seed) :
    mci_KingRowLinked Vc seed :=
  kif_kingRowLinked_of_kingDownLink Vc M (kif_kingDownLink_of_kingSegmentDown Vc M hMb hres)


theorem kif_kingInteriorConnected_of_kingSegmentDown {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {z₀ : Site 2} (hz₀ : z₀ ∈ jil_offSupportInterior Vc)
    (hres : ∀ seed : Site 2, kif_KingSegmentDown Vc seed) :
    mci_KingInteriorConnected Vc := by
  obtain ⟨M, hMb⟩ := rlc_interior_bounded Vc
  obtain ⟨seed, hseed, _⟩ := rlc_exists_lexMin_seed Vc hz₀ M
  exact ⟨seed, hseed, kif_kingRowLinked_of_kingSegmentDown Vc M hMb (hres seed)⟩


theorem kif_kingSegmentDown_body_of_downOffSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2} (hzoff : z ∉ Vc.support) (hdown : (![z 0, z 1 - 1] : Site 2) ∉ Vc.support) :
    ∃ cx : ℤ, z 0 ≤ cx ∧
      (∀ t : ℤ, z 0 ≤ t → t ≤ cx → (![t, z 1] : Site 2) ∉ Vc.support) ∧
      ((![cx, z 1 - 1] : Site 2) ∉ Vc.support ∨
        ((![cx + 1, z 1] : Site 2) ∉ Vc.support ∧
          (![cx + 1, z 1 - 1] : Site 2) ∉ Vc.support)) := by
  obtain ⟨cx, hxcx, hrun, hcdown⟩ :=
    rlc_segmentDown_body_of_downOffSupport Vc hzoff hdown
  exact ⟨cx, hxcx, hrun, Or.inl hcdown⟩


theorem kif_kingSegmentDown_body_via_diagDR {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z0 z1 : ℤ}
    (hzoff : (![z0, z1] : Site 2) ∉ Vc.support)
    (helbow : (![z0 + 1, z1] : Site 2) ∉ Vc.support)
    (hdiag : (![z0 + 1, z1 - 1] : Site 2) ∉ Vc.support) :
    ∃ cx : ℤ, z0 ≤ cx ∧
      (∀ t : ℤ, z0 ≤ t → t ≤ cx → (![t, z1] : Site 2) ∉ Vc.support) ∧
      ((![cx, z1 - 1] : Site 2) ∉ Vc.support ∨
        ((![cx + 1, z1] : Site 2) ∉ Vc.support ∧
          (![cx + 1, z1 - 1] : Site 2) ∉ Vc.support)) := by
  refine ⟨z0, le_rfl, ?_, Or.inr ⟨helbow, hdiag⟩⟩
  intro t ht ht'
  have : t = z0 := le_antisymm ht' ht
  subst this
  exact hzoff


theorem kif_fjord_on_70 : (![7, 0] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; right; left
  exact sdc_vsegUp_mem' 7 0 4 0 (by norm_num) (by norm_num)


theorem kif_fjord_body_false :
    ¬ ∃ cx : ℤ, (5 : ℤ) ≤ cx ∧
        (∀ t : ℤ, (5 : ℤ) ≤ t → t ≤ cx → (![t, 1] : Site 2) ∉ sdc_fjord.support) ∧
        ((![cx, 1 - 1] : Site 2) ∉ sdc_fjord.support ∨
          ((![cx + 1, 1] : Site 2) ∉ sdc_fjord.support ∧
            (![cx + 1, 1 - 1] : Site 2) ∉ sdc_fjord.support)) := by
  rintro ⟨cx, hxcx, hrun, hdesc⟩
  
  have hcx6 : cx ≤ 6 := by
    by_contra hcon
    push Not at hcon
    exact hrun 7 (by norm_num) (by omega) sdc_fjord_on_71
  have hcx5 : cx = 5 ∨ cx = 6 := by omega
  rcases hdesc with hdown | ⟨_helbow, hdiag⟩
  · 
    have : (![cx, (1 : ℤ) - 1] : Site 2) ∈ sdc_fjord.support := by
      rcases hcx5 with h | h <;> subst h
      · simpa using sdc_fjord_on_50
      · simpa using sdc_fjord_on_60
    exact hdown this
  · 
    have : (![cx + 1, (1 : ℤ) - 1] : Site 2) ∈ sdc_fjord.support := by
      rcases hcx5 with h | h <;> subst h
      · simpa using sdc_fjord_on_60
      · simpa using kif_fjord_on_70
    exact hdiag this


theorem kif_fjord_kingSegmentDown_false :
    ∃ (seed : Site 2), seed ∈ jil_offSupportInterior sdc_fjord ∧
      ¬ kif_KingSegmentDown sdc_fjord seed := by
  obtain ⟨M, hMb⟩ := rlc_interior_bounded sdc_fjord
  obtain ⟨seed, hseed, hmin⟩ :=
    rlc_exists_lexMin_seed sdc_fjord sdc_fjord_mem_interior_11 M
  refine ⟨seed, hseed, ?_⟩
  intro hres
  have hbox11 := hMb _ sdc_fjord_interior_11
  have hbox51 := hMb _ sdc_fjord_interior_51
  have hlt : rlc_lexMeasure M (![1, 1] : Site 2) < rlc_lexMeasure M (![5, 1] : Site 2) := by
    obtain ⟨⟨h0a, h0b⟩, ⟨h1a, h1b⟩⟩ := hbox11
    obtain ⟨⟨g0a, g0b⟩, ⟨g1a, g1b⟩⟩ := hbox51
    refine rlc_lexMeasure_lt (z := (![5, 1] : Site 2)) (z' := (![1, 1] : Site 2))
      (by simpa using g0a) (by simpa using g0b) (by simpa using g1a) (by simpa using g1b)
      (by simpa using h0a) (by simpa using h0b) (by simpa using h1a) (by simpa using h1b)
      (Or.inr ⟨by norm_num, by norm_num⟩)
  have hseedne : seed ≠ (![5, 1] : Site 2) := by
    intro heq
    have := hmin _ sdc_fjord_mem_interior_11
    rw [heq] at this
    omega
  have hleft : (![(![5, 1] : Site 2) 0 - 1, (![5, 1] : Site 2) 1] : Site 2) ∈ sdc_fjord.support := by
    simpa using sdc_fjord_on_41
  obtain ⟨cx, hxcx, hrun, hdesc⟩ :=
    hres (![5, 1] : Site 2) sdc_fjord_mem_interior_51 (fun h => hseedne h.symm) hleft
  refine kif_fjord_body_false ⟨cx, by simpa using hxcx, ?_, ?_⟩
  · intro t ht ht'
    have := hrun t (by simpa using ht) ht'
    simpa using this
  · rcases hdesc with hdown | ⟨helbow, hdiag⟩
    · exact Or.inl (by simpa using hdown)
    · exact Or.inr ⟨by simpa using helbow, by simpa using hdiag⟩

end Lattice
end StatMech
