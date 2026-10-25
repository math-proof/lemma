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
import Def.StatisticalMechanics.Code.Walls.wosorientedsign
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


theorem wos_signsAlternate_columnAlternates (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : wos_SignsAlternateInColumnOrder z w) :
    wna_ColumnAlternates z w :=
  wcb_columnAlternates_of_sorted_alt z w h


theorem wos_signedCross_abs_le_one (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : wos_SignsAlternateInColumnOrder z w) :
    |wnd_signedCross z w| ≤ 1 :=
  wna_signedCross_abs_le_one_of_columnAlternates z w (wos_signsAlternate_columnAlternates z w h)


theorem wos_signedCross_pm_one (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : wos_SignsAlternateInColumnOrder z w)
    (hodd : ¬ Even (jec_rayCount z w)) :
    wnd_signedCross z w = 1 ∨ wnd_signedCross z w = -1 :=
  wna_signedCross_pm_one_of_columnAlternates z w (wos_signsAlternate_columnAlternates z w h) hodd


theorem wos_alt_eq_of_len_head {L M : List ℤ} (hL : wnu_Alt L) (hM : wnu_Alt M)
    (hlen : L.length = M.length) (hhead : L.headI = M.headI) : L = M := by
  induction L generalizing M with
  | nil => cases M with
    | nil => rfl
    | cons b t => simp at hlen
  | cons a s ih =>
    cases M with
    | nil => simp at hlen
    | cons b u =>
      simp only [List.headI] at hhead
      subst hhead
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      cases s with
      | nil =>
        cases u with
        | nil => rfl
        | cons => simp at hlen
      | cons s0 s' =>
        cases u with
        | nil => simp at hlen
        | cons u0 u' =>
          
          have hsa := (wnu_Alt_cons_cons.mp hL).2.1   
          have hua := (wnu_Alt_cons_cons.mp hM).2.1   
          have htL : wnu_Alt (s0 :: s') := (wnu_Alt_cons_cons.mp hL).2.2
          have htM : wnu_Alt (u0 :: u') := (wnu_Alt_cons_cons.mp hM).2.2
          have hheadT : (s0 :: s').headI = (u0 :: u').headI := by
            simp only [List.headI]; rw [hsa, hua]
          have := ih (M := u0 :: u') htL htM (by simpa using hlen) hheadT
          rw [this]


theorem wos_alt_map_neg {L : List ℤ} (h : wnu_Alt L) : wnu_Alt (L.map (fun x => -x)) := by
  induction L with
  | nil => simp
  | cons a s ih =>
    cases s with
    | nil =>
      rcases (wnu_Alt_singleton a).mp h with h1 | h1 <;> subst h1 <;> simp
    | cons b t =>
      obtain ⟨ha, hba, htl⟩ := wnu_Alt_cons_cons.mp h
      simp only [List.map_cons]
      rw [wnu_Alt_cons_cons]
      refine ⟨?_, by rw [hba]; try ring, ?_⟩
      · rcases ha with h1 | h1 <;> subst h1 <;> simp
      · have := ih htl
        simpa using this


theorem wos_nonzeroDiffs_head_one (f : ℕ → ℤ)
    (h01 : ∀ n, f n = 0 ∨ f n = 1) (h0 : f 0 = 0) (n : ℕ)
    (hne : wis_nonzeroDiffs f n ≠ []) :
    (wis_nonzeroDiffs f n).headI = 1 := by
  
  
  set D := wis_nonzeroDiffs f n with hD
  obtain ⟨d, t, hdt⟩ := List.exists_cons_of_ne_nil hne
  have hhead : D.headI = d := by rw [hdt]; rfl
  
  have hpm : ∀ e ∈ D, e = 1 ∨ e = -1 := by
    intro e he
    rw [hD, wis_nonzeroDiffs, List.mem_filter] at he
    obtain ⟨hmem, hnee⟩ := he
    rw [List.mem_map] at hmem
    obtain ⟨i, _, rfl⟩ := hmem
    have := h01 (i + 1); have := h01 i
    simp only [ne_eq, decide_eq_true_eq] at hnee
    omega
  have hd_pm : d = 1 ∨ d = -1 := hpm d (by rw [hdt]; exact List.mem_cons_self ..)
  
  have htake : D.take 1 = [d] := by rw [hdt]; rfl
  obtain ⟨m, _, hm⟩ := wis_take_nonzeroDiffs f n 1
  rw [← hD] at hm
  have hsum1 : (D.take 1).sum = f m := by rw [hm, wis_nonzeroDiffs_sum f h0 m]
  rw [htake] at hsum1
  simp only [List.sum_cons, List.sum_nil, add_zero] at hsum1
  have hfm := h01 m
  rw [hhead]
  rcases hd_pm with h | h
  · exact h
  · exfalso; rw [h] at hsum1; omega


theorem wos_indNonzeroDiffs_alternates (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (c₀ : ℤ) (N : ℕ)
    (hbase : wis_indSeq z Vc c₀ 0 = 0) :
    wnu_Alt (wis_nonzeroDiffs (wis_indSeq z Vc c₀) N) := by
  obtain ⟨ind, hpm, hind0, hind01, hstep⟩ :=
    wis_nonzeroDiffs_isIndicatorStep (wis_indSeq z Vc c₀)
      (fun m => wis_indSeq_in_01 z Vc c₀ m) hbase N
  exact wst_alt_of_indicatorSteps _ ind hpm hind01 hind0 hstep


end Lattice
end StatMech
