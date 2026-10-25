/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean -/

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
import Def.StatisticalMechanics.Code.Walls.wosorientedsign.Part2
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


theorem wos_nonzeroDiffs_neg (f : ℕ → ℤ) (n : ℕ) :
    wis_nonzeroDiffs (fun i => - f i) n = (wis_nonzeroDiffs f n).map (fun x => -x) := by
  unfold wis_nonzeroDiffs
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.filter_append,
      List.filter_append, List.map_append, ih]
    congr 1
    simp only [List.map_cons, List.map_nil]
    by_cases hd : f (k + 1) - f k = 0
    · have hd' : (fun i => - f i) (k + 1) - (fun i => - f i) k = 0 := by simp only; omega
      rw [List.filter_cons_of_neg (by simp only [decide_eq_true_eq, ne_eq, not_not]; exact hd'),
          List.filter_cons_of_neg (by simp only [decide_eq_true_eq, ne_eq, not_not]; exact hd)]
      simp
    · have hd' : (fun i => - f i) (k + 1) - (fun i => - f i) k ≠ 0 := by simp only; omega
      rw [List.filter_cons_of_pos (by simp only [decide_eq_true_eq, ne_eq]; exact hd'),
          List.filter_cons_of_pos (by simp only [decide_eq_true_eq, ne_eq]; exact hd)]
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · show - f (k + 1) - (- f k) = -(f (k + 1) - f k); ring
      · rfl


theorem wos_signEqIndicatorJumps_of_alternate (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (halt : wos_SignsAlternateInColumnOrder z Vc)
    (hlen : wos_IndicatorLenEq z Vc) :
    wis_SignEqIndicatorJumps z Vc := by
  obtain ⟨c₀, N, hbase, hlenEq⟩ := hlen
  set D := wis_nonzeroDiffs (wis_indSeq z Vc c₀) N with hD
  have hDalt : wnu_Alt D := wos_indNonzeroDiffs_alternates z Vc c₀ N hbase
  have hCalt : wnu_Alt (wcb_columnSorted z Vc) := halt
  have hperm : (wcb_columnSorted z Vc).Perm (wnu_signedList z Vc) :=
    wcb_columnOrder_permutes_signedList z Vc
  refine ⟨c₀, N, hbase, ?_⟩
  rw [← hD]
  
  by_cases hlenz : (wcb_columnSorted z Vc).length = 0
  · 
    have hDempty : D = [] := List.length_eq_zero_iff.mp (by rw [hlenEq, hlenz])
    have hCempty : wcb_columnSorted z Vc = [] := List.length_eq_zero_iff.mp hlenz
    left
    rw [hDempty]
    rw [hCempty] at hperm
    exact hperm
  · 
    have hDne : D ≠ [] := by
      intro h; apply hlenz; rw [← hlenEq, h]; simp
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
      have hDeqC : D = wcb_columnSorted z Vc :=
        wos_alt_eq_of_len_head hDalt hCalt hlenEq (by rw [hDhead, hCp])
      rw [hDeqC]; exact hperm
    · 
      right
      
      have hnegD : (D.map (fun x => -x)) = wcb_columnSorted z Vc := by
        apply wos_alt_eq_of_len_head (wos_alt_map_neg hDalt) hCalt
        · simp [hlenEq]
        · 
          obtain ⟨d, t, hdt⟩ := List.exists_cons_of_ne_nil hDne
          rw [hdt, List.map_cons]
          simp only [List.headI]
          have hd1 : d = 1 := by rw [← hDhead, hdt]; rfl
          rw [hd1]
          exact hCm.symm
      
      have hDnegList : wis_nonzeroDiffs (fun i => - wis_indSeq z Vc c₀ i) N
          = D.map (fun x => -x) :=
        (wos_nonzeroDiffs_neg (wis_indSeq z Vc c₀) N).trans (by rw [hD])
      rw [hDnegList, hnegD]
      exact hperm


theorem wos_unitSquare_signsAlternate :
    wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) wwit_unitSquareLoop := by
  unfold wos_SignsAlternateInColumnOrder
  rw [wcb_unitSquare_columnSorted]
  exact Or.inl rfl


theorem wos_Ltromino_signsAlternate :
    wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) wnu_LtrominoLoop := by
  unfold wos_SignsAlternateInColumnOrder
  rw [wcb_Ltromino_columnSorted]
  exact Or.inr rfl


theorem wos_unitSquare_columnAlternates :
    wna_ColumnAlternates (![1, 1] : Site 2) wwit_unitSquareLoop :=
  wos_signsAlternate_columnAlternates _ _ wos_unitSquare_signsAlternate


theorem wos_Ltromino_columnAlternates :
    wna_ColumnAlternates (![1, 1] : Site 2) wnu_LtrominoLoop :=
  wos_signsAlternate_columnAlternates _ _ wos_Ltromino_signsAlternate


theorem wos_twoToggle_alternates : wnu_Alt ([1, -1] : List ℤ) := by
  refine ⟨Or.inl rfl, by norm_num, ?_⟩
  exact Or.inr rfl


theorem wos_twoToggle_neg_alternates : wnu_Alt ([-1, 1] : List ℤ) := by
  refine ⟨Or.inr rfl, by norm_num, ?_⟩
  exact Or.inl rfl


theorem wos_twoToggle_eq (M : List ℤ) (hM : wnu_Alt M) (hlen : M.length = 2)
    (hhead : M.headI = 1) : M = [1, -1] := by
  have := wos_alt_eq_of_len_head hM wos_twoToggle_alternates (by simp [hlen]) (by simp [hhead])
  exact this


theorem wos_doubleSquare_list_not_alternates : ¬ wnu_Alt ([1, 1] : List ℤ) := by
  intro h
  have := (wnu_Alt_cons_cons.mp h).2.1
  norm_num at this


theorem wos_doubleSquare_not_signsAlternate :
    ¬ wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) wnu_doubleSquare := by
  unfold wos_SignsAlternateInColumnOrder
  rw [wcb_doubleSquare_columnSorted]
  exact wos_doubleSquare_list_not_alternates

end Lattice
end StatMech
