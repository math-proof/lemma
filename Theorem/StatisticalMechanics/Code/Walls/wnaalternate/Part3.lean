/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.umffullrev.Part2
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
import Def.StatisticalMechanics.Code.Walls.wnaalternate.Part2
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

theorem wna_signedCross_abs_le_one_of_columnAlternates (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : wna_ColumnAlternates z w) :
    |wnd_signedCross z w| ≤ 1 := by
  obtain ⟨M, hperm, halt⟩ := h
  have hsum : M.sum = wnd_signedCross z w := by
    rw [hperm.sum_eq]; exact wnu_signedList_sum z w
  rw [← hsum]
  exact wnu_altSum_abs_le_one M halt


theorem wna_signedCross_pm_one_of_columnAlternates (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : wna_ColumnAlternates z w)
    (hodd : ¬ Even (jec_rayCount z w)) :
    wnd_signedCross z w = 1 ∨ wnd_signedCross z w = -1 := by
  obtain ⟨M, hperm, halt⟩ := h
  have hsum : M.sum = wnd_signedCross z w := by
    rw [hperm.sum_eq]; exact wnu_signedList_sum z w
  have hne : M.sum ≠ 0 := by
    rw [hsum]; exact wnd_signedCross_ne_zero_of_rayCount_odd z w hodd
  rw [← hsum]
  exact wnu_altSum_pm_one_of_ne_zero M halt hne


theorem wna_alternates_of_signedList_alt (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : wnu_Alt (wnu_signedList z w)) :
    wnu_Alternates z w := h


theorem wna_alternates_of_columnAlternates_id (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (h : wnu_Alt (wnu_signedList z w)) :
    wna_ColumnAlternates z w :=
  ⟨wnu_signedList z w, List.Perm.refl _, h⟩


theorem wna_unitSquare_columnAlternates :
    wna_ColumnAlternates (![1, 1] : Site 2) wwit_unitSquareLoop :=
  wna_alternates_of_columnAlternates_id _ _ wnu_unitSquare_alternates


theorem wna_unitSquare_signedCross_abs_le_one :
    |wnd_signedCross (![1, 1] : Site 2) wwit_unitSquareLoop| ≤ 1 :=
  wna_signedCross_abs_le_one_of_columnAlternates _ _ wna_unitSquare_columnAlternates


theorem wna_Ltromino_columnAlternates :
    wna_ColumnAlternates (![1, 1] : Site 2) wnu_LtrominoLoop :=
  wna_alternates_of_columnAlternates_id _ _ wnu_Ltromino_alternates


theorem wna_Ltromino_signedCross_abs_le_one :
    |wnd_signedCross (![1, 1] : Site 2) wnu_LtrominoLoop| ≤ 1 :=
  wna_signedCross_abs_le_one_of_columnAlternates _ _ wna_Ltromino_columnAlternates


theorem wna_toggle_on_singleton :
    wnu_Alt [(1 : ℤ)] := by
  apply wna_alt_of_prefixSums_in_01
  · intro x hx; simp at hx; omega
  · intro p hp; unfold wna_prefixSums at hp; simp at hp; omega


theorem wna_doubleSquare_not_columnAlternates :
    ¬ wna_ColumnAlternates (![1, 1] : Site 2) wnu_doubleSquare := by
  rintro ⟨M, hperm, halt⟩
  rw [wnu_doubleSquare_signedList] at hperm
  
  have hM : M = [1, 1] := by
    have hlen := hperm.length_eq
    have hmem : ∀ x ∈ M, x = 1 := by
      intro x hx
      have hx2 := hperm.mem_iff.mp hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx2
      rcases hx2 with h | h <;> exact h
    
    match M, hlen with
    | [a, b], _ =>
      have ha := hmem a (by simp)
      have hb := hmem b (by simp)
      rw [ha, hb]
  rw [hM] at halt
  exact wnu_not_alt_oneOne halt


theorem wna_doubleSquare_prefix_leaves_01 :
    ∃ p ∈ wna_prefixSums [(1 : ℤ), 1], ¬ (p = 0 ∨ p = 1) := by
  refine ⟨2, ?_, by omega⟩
  unfold wna_prefixSums; simp


theorem wna_signedCrossPMone_of_columnAlternates (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (halt : wna_ColumnAlternates z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2))) :
    wnd_SignedCrossPMone K hK a z := by
  unfold wnd_SignedCrossPMone
  exact wna_signedCross_pm_one_of_columnAlternates z (olb_orbitLoop K hK a.1 a.2) halt hodd


theorem wna_revCount_pm_one_of_columnAlternates_bridge (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (halt : wna_ColumnAlternates z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
    (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
    revCount K a = 1 ∨ revCount K a = -1 :=
  wnd_revCount_pm_one_of_residues K hK a z hbridge
    (wna_signedCrossPMone_of_columnAlternates K hK a z halt hodd)


theorem wna_eulerCharOne_of_columnAlternates_bridge (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hp : 3 ≤ dartOrbitPeriod K a)
    (halt : wna_ColumnAlternates z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
    (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
    EulerCharOne K a :=
  wnd_eulerCharOne_of_residues K hK a z hp hbridge
    (wna_signedCrossPMone_of_columnAlternates K hK a z halt hodd)


end Lattice
end StatMech
