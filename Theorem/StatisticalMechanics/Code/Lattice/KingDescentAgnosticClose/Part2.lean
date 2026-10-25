/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.KingInteriorFloodClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.KingSegmentDownClose
import Def.StatisticalMechanics.Code.Lattice.KingDescentAgnosticClose.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem kda_kingAdj_downLeft (x y : ℤ) :
    mci_kingGraph.Adj (![x, y] : Site 2) ![x - 1, y - 1] := by
  have h := mci_kingAdj_diag x y (-1) (-1) (Or.inr rfl) (Or.inr rfl)
  simpa only [show x + (-1) = x - 1 by ring, show y + (-1) = y - 1 by ring] using h


theorem kda_kingAdj_downRight (x y : ℤ) :
    mci_kingGraph.Adj (![x, y] : Site 2) ![x + 1, y - 1] := by
  have h := mci_kingAdj_diag x y 1 (-1) (Or.inl rfl) (Or.inr rfl)
  simpa only [show y + (-1) = y - 1 by ring] using h


theorem kda_descentStep_to_neighbour {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y : ℤ} (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    {w : Site 2} (hw : w ∈ jil_offSupportInterior Vc)
    (hadj : mci_kingGraph.Adj (![x, y] : Site 2) w)
    (hlex : w 1 < y ∨ (w 1 = y ∧ w 0 < x)) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z',
        ∀ u ∈ p.support, u ∈ jil_offSupportInterior Vc := by
  refine ⟨w, hw, ?_, ?_⟩
  · have hzL := (jil_mem_offSupportInterior Vc _ |>.mp hz).2
    have hwL := (jil_mem_offSupportInterior Vc _ |>.mp hw).2
    obtain ⟨⟨hb0a, hb0b⟩, ⟨hb1a, hb1b⟩⟩ := hMb _ hzL
    obtain ⟨⟨hd0a, hd0b⟩, ⟨hd1a, hd1b⟩⟩ := hMb _ hwL
    refine rlc_lexMeasure_lt (z := (![x, y] : Site 2)) (z' := w)
      (by simpa using hb0a) (by simpa using hb0b) (by simpa using hb1a) (by simpa using hb1b)
      hd0a hd0b hd1a hd1b ?_
    simpa using hlex
  · refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
    intro u hu
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with h | h
    · subst h; exact hz
    · subst h; exact hw


theorem kda_kingDownLink_of_descentStep {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ)
    (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    (hres : kda_KingDescentStep Vc seed) :
    kif_KingDownLink Vc seed M := by
  intro z hz hzs
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  rw [hzeq] at hz ⊢
  rcases hres z (hzeq ▸ hz) hzs with hL | hDL | hD | hDR
  · 
    exact kda_descentStep_to_neighbour Vc M hMb hz (by simpa using hL)
      (by simpa using kif_kingAdj_left (z 0) (z 1)) (Or.inr ⟨by simp, by simp⟩)
  · 
    exact kda_descentStep_to_neighbour Vc M hMb hz (by simpa using hDL)
      (by simpa using kda_kingAdj_downLeft (z 0) (z 1)) (Or.inl (by simp))
  · 
    exact kda_descentStep_to_neighbour Vc M hMb hz (by simpa using hD)
      (by simpa using kif_kingAdj_down (z 0) (z 1)) (Or.inl (by simp))
  · 
    exact kda_descentStep_to_neighbour Vc M hMb hz (by simpa using hDR)
      (by simpa using kda_kingAdj_downRight (z 0) (z 1)) (Or.inl (by simp))


theorem kda_kingRowLinked_of_descentStep {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ)
    (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    (hres : kda_KingDescentStep Vc seed) :
    mci_KingRowLinked Vc seed :=
  kif_kingRowLinked_of_kingDownLink Vc M (kda_kingDownLink_of_descentStep Vc M hMb hres)


theorem kda_seed_is_31 {M : ℤ}
    (hMb : ∀ z ∈ jec_leftRegion kda_stairDR, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {seed : Site 2} (hseed : seed ∈ jil_offSupportInterior kda_stairDR)
    (hmin : ∀ z ∈ jil_offSupportInterior kda_stairDR,
      rlc_lexMeasure M seed ≤ rlc_lexMeasure M z) :
    seed = (![3, 1] : Site 2) := by
  have hmem : seed ∈ ({(![1, 2] : Site 2), (![2, 2] : Site 2), (![3, 1] : Site 2)} : Set (Site 2)) := by
    rw [← kda_interior_eq]; exact hseed
  have hbox31 := hMb _ kda_interior_31
  obtain ⟨⟨g0a, g0b⟩, ⟨g1a, g1b⟩⟩ := hbox31
  rcases hmem with h | h | h
  · exfalso
    have hbox12 := hMb _ kda_interior_12
    obtain ⟨⟨h0a, h0b⟩, ⟨h1a, h1b⟩⟩ := hbox12
    have hlt : rlc_lexMeasure M (![3, 1] : Site 2) < rlc_lexMeasure M (![1, 2] : Site 2) :=
      rlc_lexMeasure_lt (z := (![1, 2] : Site 2)) (z' := (![3, 1] : Site 2))
        (by simpa using h0a) (by simpa using h0b) (by simpa using h1a) (by simpa using h1b)
        (by simpa using g0a) (by simpa using g0b) (by simpa using g1a) (by simpa using g1b)
        (Or.inl (by norm_num))
    have := hmin _ kda_mem_interior_31
    rw [h] at this; omega
  · exfalso
    have hbox22 := hMb _ kda_interior_22
    obtain ⟨⟨h0a, h0b⟩, ⟨h1a, h1b⟩⟩ := hbox22
    have hlt : rlc_lexMeasure M (![3, 1] : Site 2) < rlc_lexMeasure M (![2, 2] : Site 2) :=
      rlc_lexMeasure_lt (z := (![2, 2] : Site 2)) (z' := (![3, 1] : Site 2))
        (by simpa using h0a) (by simpa using h0b) (by simpa using h1a) (by simpa using h1b)
        (by simpa using g0a) (by simpa using g0b) (by simpa using g1a) (by simpa using g1b)
        (Or.inl (by norm_num))
    have := hmin _ kda_mem_interior_31
    rw [h] at this; omega
  · exact h


theorem kda_stairDR_descentStep_false :
    ¬ kda_KingDescentStep kda_stairDR (![3, 1] : Site 2) := by
  intro hres
  have hne : (![1, 2] : Site 2) ≠ (![3, 1] : Site 2) := by
    intro h; have := congrFun h 0; simp at this
  have hcoords : ((![1, 2] : Site 2) 0 = 1) ∧ ((![1, 2] : Site 2) 1 = 2) := ⟨by simp, by simp⟩
  obtain ⟨hc0, hc1⟩ := hcoords
  
  rcases hres (![1, 2] : Site 2) kda_mem_interior_12 hne with hL | hDL | hD | hDR
  · exact (jil_mem_offSupportInterior kda_stairDR _ |>.mp hL).1
      (by simpa only [hc0, hc1, show (1:ℤ) - 1 = 0 by ring] using kda_on_02)
  · exact (jil_mem_offSupportInterior kda_stairDR _ |>.mp hDL).1
      (by simpa only [hc0, hc1, show (1:ℤ) - 1 = 0 by ring, show (2:ℤ) - 1 = 1 by ring]
        using kda_on_01)
  · exact (jil_mem_offSupportInterior kda_stairDR _ |>.mp hD).1
      (by simpa only [hc0, hc1, show (2:ℤ) - 1 = 1 by ring] using kda_on_11)
  · exact (jil_mem_offSupportInterior kda_stairDR _ |>.mp hDR).1
      (by simpa only [hc0, hc1, show (1:ℤ) + 1 = 2 by ring, show (2:ℤ) - 1 = 1 by ring]
        using kda_on_21)


theorem kda_descentStep_lexMinSeed_false :
    ∃ seed : Site 2, seed ∈ jil_offSupportInterior kda_stairDR ∧
      ¬ kda_KingDescentStep kda_stairDR seed := by
  obtain ⟨M, hMb⟩ := rlc_interior_bounded kda_stairDR
  obtain ⟨seed, hseed, hmin⟩ :=
    rlc_exists_lexMin_seed kda_stairDR kda_mem_interior_31 M
  refine ⟨seed, hseed, ?_⟩
  rw [kda_seed_is_31 hMb hseed hmin]
  exact kda_stairDR_descentStep_false


theorem kda_stairDR_kingRowLinked : mci_KingRowLinked kda_stairDR (![3, 1] : Site 2) := by
  
  have hadj_r : mci_kingGraph.Adj (![1, 2] : Site 2) (![2, 2] : Site 2) := by
    simpa using kif_kingAdj_right 1 2
  have hadj_dr : mci_kingGraph.Adj (![2, 2] : Site 2) (![3, 1] : Site 2) := by
    have h := kda_kingAdj_downRight 2 2
    simpa only [show (2:ℤ) + 1 = 3 by ring, show (2:ℤ) - 1 = 1 by ring] using h
  intro z hz
  have hmem : z ∈ ({(![1, 2] : Site 2), (![2, 2] : Site 2), (![3, 1] : Site 2)}
      : Set (Site 2)) := by
    rw [← kda_interior_eq]; exact hz
  rcases hmem with h | h | h
  · 
    subst h
    refine ⟨SimpleGraph.Walk.cons hadj_r (SimpleGraph.Walk.cons hadj_dr SimpleGraph.Walk.nil), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h
    · subst h; exact kda_mem_interior_12
    · subst h; exact kda_mem_interior_22
    · subst h; exact kda_mem_interior_31
  · 
    subst h
    refine ⟨SimpleGraph.Walk.cons hadj_dr SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h
    · subst h; exact kda_mem_interior_22
    · subst h; exact kda_mem_interior_31
  · 
    subst h
    exact ⟨SimpleGraph.Walk.nil, by
      intro w hw
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
      exact hw ▸ kda_mem_interior_31⟩


theorem kda_descentStep_false_but_theorem_true :
    mci_FourThin kda_stairDR ∧
    mci_KingRowLinked kda_stairDR (![3, 1] : Site 2) ∧
    ¬ kda_KingDescentStep kda_stairDR (![3, 1] : Site 2) :=
  ⟨kda_stairDR_fourThin, kda_stairDR_kingRowLinked, kda_stairDR_descentStep_false⟩

end Lattice
end StatMech
