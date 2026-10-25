/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
import Theorem.StatisticalMechanics.Code.Walls.wcbcolumnbridge.Part4
import Theorem.StatisticalMechanics.Code.Walls.wstsigntoggle.Part2
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
import Theorem.StatisticalMechanics.Code.Walls.wisindicatorsteps.Part5
import Theorem.StatisticalMechanics.Code.Walls.wosorientedsign.Part2
import Theorem.StatisticalMechanics.Code.Walls.welenterleave.Part2
import Theorem.StatisticalMechanics.Code.Walls.woborientbridge.Part4
import Def.StatisticalMechanics.Code.Walls.wpdprimaldegree
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


theorem wpd_upEntersInterior_iff_orientationConsistent (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) :
    wpd_UpEntersInterior z Vc ↔ wel_OrientationConsistent z Vc := Iff.rfl


theorem wpd_orientationConsistent_of_upEntersInterior (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wpd_UpEntersInterior z Vc) :
    wel_OrientationConsistent z Vc := h


theorem wpd_signsAlternate_of_upEntersInterior (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wpd_UpEntersInterior z Vc) :
    wos_SignsAlternateInColumnOrder z Vc :=
  wel_signsAlternate_of_orientationConsistent z Vc h


theorem wpd_columnAlternates_of_upEntersInterior (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wpd_UpEntersInterior z Vc) :
    wna_ColumnAlternates z Vc :=
  wel_columnAlternates_of_orientationConsistent z Vc h


theorem wpd_signedCross_pm_one_of_upEntersInterior (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : wpd_UpEntersInterior z Vc)
    (hodd : ¬ Even (jec_rayCount z Vc)) :
    wnd_signedCross z Vc = 1 ∨ wnd_signedCross z Vc = -1 :=
  wel_signedCross_pm_one z Vc h hodd


theorem wpd_upEntersInterior_of_alternate (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (halt : wos_SignsAlternateInColumnOrder z Vc)
    (hlen : wos_IndicatorLenEq z Vc) :
    wpd_UpEntersInterior z Vc := by
  obtain ⟨c₀, N, hbase, hlenEq⟩ := hlen
  refine ⟨c₀, N, hbase, ?_⟩
  set D := wis_nonzeroDiffs (wis_indSeq z Vc c₀) N with hD
  have hDalt : wnu_Alt D := wos_indNonzeroDiffs_alternates z Vc c₀ N hbase
  have hCalt : wnu_Alt (wcb_columnSorted z Vc) := halt
  by_cases hlenz : (wcb_columnSorted z Vc).length = 0
  · 
    have hDempty : D = [] := List.length_eq_zero_iff.mp (by rw [hlenEq, hlenz])
    have hCempty : wcb_columnSorted z Vc = [] := List.length_eq_zero_iff.mp hlenz
    exact Or.inl (by rw [hCempty, hDempty])
  · have hDne : D ≠ [] := by intro h; apply hlenz; rw [← hlenEq, h]; simp
    have hCne : wcb_columnSorted z Vc ≠ [] := fun h => hlenz (by rw [h]; simp)
    have hDhead : D.headI = 1 :=
      wos_nonzeroDiffs_head_one (wis_indSeq z Vc c₀)
        (fun m => wis_indSeq_in_01 z Vc c₀ m) hbase N hDne
    have hChead : (wcb_columnSorted z Vc).headI = 1 ∨ (wcb_columnSorted z Vc).headI = -1 := by
      obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hCne
      have := wnu_Alt_head_pm (hct ▸ hCalt)
      rw [hct]; simpa using this
    rcases hChead with hCp | hCm
    · 
      left
      exact (wos_alt_eq_of_len_head hCalt hDalt hlenEq.symm (by rw [hCp, hDhead]))
    · 
      right
      apply wos_alt_eq_of_len_head hCalt (wos_alt_map_neg hDalt)
      · simp [hlenEq]
      · obtain ⟨d, t, hdt⟩ := List.exists_cons_of_ne_nil hDne
        have hd1 : d = 1 := by rw [← hDhead, hdt]; rfl
        rw [hCm, hdt, List.map_cons]
        simp only [List.headI, hd1]


theorem wpd_upEntersInterior_iff_alternate_and_len (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) :
    wpd_UpEntersInterior z Vc ↔
      (wos_SignsAlternateInColumnOrder z Vc ∧ wos_IndicatorLenEq z Vc) := by
  constructor
  · intro h
    refine ⟨wpd_signsAlternate_of_upEntersInterior z Vc h, ?_⟩
    
    obtain ⟨c₀, N, hbase, hbranch⟩ := h
    refine ⟨c₀, N, hbase, ?_⟩
    rcases hbranch with hEq | hEqNeg
    · rw [hEq]
    · rw [hEqNeg]; simp
  · rintro ⟨halt, hlen⟩; exact wpd_upEntersInterior_of_alternate z Vc halt hlen


theorem wpd_unitSquare_upEntersInterior :
    wpd_UpEntersInterior (![1, 1] : Site 2) wwit_unitSquareLoop :=
  (wob_columnSortedEqJumps_iff_orientationConsistent _ _).mp wob_unitSquare_columnSortedEqJumps


theorem wpd_Ltromino_upEntersInterior :
    wpd_UpEntersInterior (![1, 1] : Site 2) wnu_LtrominoLoop :=
  (wob_columnSortedEqJumps_iff_orientationConsistent _ _).mp wob_Ltromino_columnSortedEqJumps


theorem wpd_doubleSquare_not_upEntersInterior :
    ¬ wpd_UpEntersInterior (![1, 1] : Site 2) wnu_doubleSquare :=
  wel_doubleSquare_not_orientationConsistent

end Lattice
end StatMech
