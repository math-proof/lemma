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
import Def.StatisticalMechanics.Code.Lattice.KingInteriorFloodClose
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem kif_kingRowLinked_of_kingDownLink {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ) (hdl : kif_KingDownLink Vc seed M) :
    mci_KingRowLinked Vc seed := by
  have key : ∀ n : ℕ, ∀ z ∈ jil_offSupportInterior Vc, rlc_lexMeasure M z = n →
      ∃ p : mci_kingGraph.Walk z seed, ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro z hz hn
      by_cases hzs : z = seed
      · cases hzs
        exact ⟨SimpleGraph.Walk.nil, by
          intro w hw
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
          cases hw; exact hz⟩
      · obtain ⟨z', hz', hlt, p, hp⟩ := hdl z hz hzs
        rw [hn] at hlt
        obtain ⟨q, hq⟩ := ih (rlc_lexMeasure M z') hlt z' hz' rfl
        refine ⟨p.append q, ?_⟩
        intro w hw
        rw [SimpleGraph.Walk.support_append, List.mem_append] at hw
        rcases hw with h | h
        · exact hp w h
        · exact hq w (List.mem_of_mem_tail h)
  intro z hz
  exact key (rlc_lexMeasure M z) z hz rfl


theorem kif_descend_via_leftStep {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hleft : (![x - 1, y] : Site 2) ∉ Vc.support) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z',
        ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
  have hz' : (![x - 1, y] : Site 2) ∈ jil_offSupportInterior Vc :=
    rlc_left_mem_interior Vc hz hleft
  refine ⟨![x - 1, y], hz', ?_, ?_⟩
  · have hzL := (jil_mem_offSupportInterior Vc _ |>.mp hz).2
    have hz'L := (jil_mem_offSupportInterior Vc _ |>.mp hz').2
    obtain ⟨⟨hb0a, hb0b⟩, ⟨hb1a, hb1b⟩⟩ := hMb _ hzL
    obtain ⟨⟨hd0a, hd0b⟩, ⟨hd1a, hd1b⟩⟩ := hMb _ hz'L
    refine rlc_lexMeasure_lt hb0a hb0b hb1a hb1b (by simpa using hd0a) (by simpa using hd0b)
      (by simpa using hd1a) (by simpa using hd1b) ?_
    right; simp
  · refine ⟨SimpleGraph.Walk.cons (kif_kingAdj_left x y) SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h
    · subst h; exact hz
    · subst h; exact hz'


theorem kif_descend_via_downStep {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hdown : (![x, y - 1] : Site 2) ∉ Vc.support) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z',
        ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
  have hz' : (![x, y - 1] : Site 2) ∈ jil_offSupportInterior Vc :=
    rlc_down_mem_interior Vc hz hdown
  refine ⟨![x, y - 1], hz', ?_, ?_⟩
  · have hzL := (jil_mem_offSupportInterior Vc _ |>.mp hz).2
    have hz'L := (jil_mem_offSupportInterior Vc _ |>.mp hz').2
    obtain ⟨⟨hb0a, hb0b⟩, ⟨hb1a, hb1b⟩⟩ := hMb _ hzL
    obtain ⟨⟨hd0a, hd0b⟩, ⟨hd1a, hd1b⟩⟩ := hMb _ hz'L
    refine rlc_lexMeasure_lt hb0a hb0b hb1a hb1b (by simpa using hd0a) (by simpa using hd0b)
      (by simpa using hd1a) (by simpa using hd1b) ?_
    left; simp
  · refine ⟨SimpleGraph.Walk.cons (kif_kingAdj_down x y) SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h
    · subst h; exact hz
    · subst h; exact hz'


theorem kif_descend_via_diagDR {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (helbow : (![x + 1, y] : Site 2) ∉ Vc.support)
    (hdiag : (![x + 1, y - 1] : Site 2) ∉ Vc.support) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z',
        ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
  
  have helbowI : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc := by
    have hadj : (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x + 1, y] := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    exact mci_offSupport_neighbor_interior Vc hz hadj helbow
  
  have hdiagI : (![x + 1, y - 1] : Site 2) ∈ jil_offSupportInterior Vc := by
    have hadj : (hypercubicLattice 2).Adj (![x + 1, y] : Site 2) ![x + 1, y - 1] := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    exact mci_offSupport_neighbor_interior Vc helbowI hadj hdiag
  refine ⟨![x + 1, y - 1], hdiagI, ?_, ?_⟩
  · have hzL := (jil_mem_offSupportInterior Vc _ |>.mp hz).2
    have hz'L := (jil_mem_offSupportInterior Vc _ |>.mp hdiagI).2
    obtain ⟨⟨hb0a, hb0b⟩, ⟨hb1a, hb1b⟩⟩ := hMb _ hzL
    obtain ⟨⟨hd0a, hd0b⟩, ⟨hd1a, hd1b⟩⟩ := hMb _ hz'L
    refine rlc_lexMeasure_lt hb0a hb0b hb1a hb1b (by simpa using hd0a) (by simpa using hd0b)
      (by simpa using hd1a) (by simpa using hd1b) ?_
    left; simp
  · have hadj2 : mci_kingGraph.Adj (![x + 1, y] : Site 2) ![x + 1, y - 1] :=
      kif_kingAdj_down (x + 1) y
    refine ⟨SimpleGraph.Walk.cons (kif_kingAdj_right x y)
      (SimpleGraph.Walk.cons hadj2 SimpleGraph.Walk.nil), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h
    · subst h; exact hz
    · subst h; exact helbowI
    · subst h; exact hdiagI


theorem kif_run_kingWalk_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y cx : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hxcx : x ≤ cx)
    (hrun : ∀ t : ℤ, x ≤ t → t ≤ cx → (![t, y] : Site 2) ∉ Vc.support) :
    ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) ![cx, y],
      ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
  have hxoff : (![x, y] : Site 2) ∉ Vc.support := (jil_mem_offSupportInterior Vc _ |>.mp hz).1
  obtain ⟨preach, hpreach⟩ :=
    jil_hsegment_reachable_offSupport {p | p ∈ Vc.support} (lo := x) (hi := cx) (y := y)
      (x₁ := x) (x₂ := cx) (by simpa using hxoff) le_rfl hxcx hxcx le_rfl
      (by intro t ht ht'; simpa using hrun t ht ht')
  have hpreach' : ∀ w ∈ preach.support, w ∉ Vc.support := by
    intro w hw; have := hpreach w hw; simpa using this
  have hint := mci_offSupport_walk_interior Vc preach hpreach' hz
  refine ⟨preach.mapLe mci_hyper_le_king, ?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_mapLe_eq_support mci_hyper_le_king preach] at hw
  exact hint w hw


theorem kif_descend_via_segmentDown {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y cx : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hxcx : x ≤ cx)
    (hrun : ∀ t : ℤ, x ≤ t → t ≤ cx → (![t, y] : Site 2) ∉ Vc.support)
    (hcdown : (![cx, y - 1] : Site 2) ∉ Vc.support) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z',
        ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
  obtain ⟨pw, hpw⟩ := kif_run_kingWalk_interior Vc hz hxcx hrun
  have hc : (![cx, y] : Site 2) ∈ jil_offSupportInterior Vc :=
    hpw _ pw.end_mem_support
  have hz' : (![cx, y - 1] : Site 2) ∈ jil_offSupportInterior Vc :=
    rlc_down_mem_interior Vc hc hcdown
  refine ⟨![cx, y - 1], hz', ?_, ?_⟩
  · have hzL := (jil_mem_offSupportInterior Vc _ |>.mp hz).2
    have hz'L := (jil_mem_offSupportInterior Vc _ |>.mp hz').2
    obtain ⟨⟨hb0a, hb0b⟩, ⟨hb1a, hb1b⟩⟩ := hMb _ hzL
    obtain ⟨⟨hd0a, hd0b⟩, ⟨hd1a, hd1b⟩⟩ := hMb _ hz'L
    refine rlc_lexMeasure_lt hb0a hb0b hb1a hb1b (by simpa using hd0a) (by simpa using hd0b)
      (by simpa using hd1a) (by simpa using hd1b) ?_
    left; simp
  · refine ⟨pw.append (SimpleGraph.Walk.cons (kif_kingAdj_down cx y) SimpleGraph.Walk.nil), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hw
    rcases hw with h | h
    · exact hpw w h
    · have hmem := List.mem_of_mem_tail h
      rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h1 | h1
      · subst h1; exact hc
      · subst h1; exact hz'


theorem kif_descend_via_segmentDiagDR {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y cx : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hxcx : x ≤ cx)
    (hrun : ∀ t : ℤ, x ≤ t → t ≤ cx → (![t, y] : Site 2) ∉ Vc.support)
    (helbow : (![cx + 1, y] : Site 2) ∉ Vc.support)
    (hdiag : (![cx + 1, y - 1] : Site 2) ∉ Vc.support) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z',
        ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
  obtain ⟨pw, hpw⟩ := kif_run_kingWalk_interior Vc hz hxcx hrun
  have hc : (![cx, y] : Site 2) ∈ jil_offSupportInterior Vc :=
    hpw _ pw.end_mem_support
  
  have helbowI : (![cx + 1, y] : Site 2) ∈ jil_offSupportInterior Vc := by
    have hadj : (hypercubicLattice 2).Adj (![cx, y] : Site 2) ![cx + 1, y] := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    exact mci_offSupport_neighbor_interior Vc hc hadj helbow
  have hdiagI : (![cx + 1, y - 1] : Site 2) ∈ jil_offSupportInterior Vc := by
    have hadj : (hypercubicLattice 2).Adj (![cx + 1, y] : Site 2) ![cx + 1, y - 1] := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    exact mci_offSupport_neighbor_interior Vc helbowI hadj hdiag
  refine ⟨![cx + 1, y - 1], hdiagI, ?_, ?_⟩
  · 
    
    have hzL := (jil_mem_offSupportInterior Vc _ |>.mp hz).2
    have hz'L := (jil_mem_offSupportInterior Vc _ |>.mp hdiagI).2
    obtain ⟨⟨hb0a, hb0b⟩, ⟨hb1a, hb1b⟩⟩ := hMb _ hzL
    obtain ⟨⟨hd0a, hd0b⟩, ⟨hd1a, hd1b⟩⟩ := hMb _ hz'L
    refine rlc_lexMeasure_lt hb0a hb0b hb1a hb1b (by simpa using hd0a) (by simpa using hd0b)
      (by simpa using hd1a) (by simpa using hd1b) ?_
    left; simp
  · 
    have hadj2 : mci_kingGraph.Adj (![cx + 1, y] : Site 2) ![cx + 1, y - 1] :=
      kif_kingAdj_down (cx + 1) y
    refine ⟨pw.append (SimpleGraph.Walk.cons (kif_kingAdj_right cx y)
      (SimpleGraph.Walk.cons hadj2 SimpleGraph.Walk.nil)), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hw
    rcases hw with h | h
    · exact hpw w h
    · 
      rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil] at h
      simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h1 | h1
      · subst h1; exact helbowI
      · subst h1; exact hdiagI


end Lattice
end StatMech
