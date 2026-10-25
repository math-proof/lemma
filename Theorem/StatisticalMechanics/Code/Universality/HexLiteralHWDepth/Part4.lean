/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part3


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhr_intervalsAux_bridge (f : ℕ → ℝ) (hi fuel lo : ℕ)
    (up : Bool) (hlt : lo < hi) (hahead : HLHRAhead f up lo hi) :
    ∀ p ∈ hlhr_intervalsAux f hi fuel up lo,
      ∃ dir, HLHRBridgeInterval f dir p := by
  induction fuel generalizing lo up with
  | zero => simp [hlhr_intervalsAux]
  | succ fuel ih =>
      let k := hlhr_lastExtremum f up lo hi
      have hklo : lo < k := by
        dsimp [k]
        exact hlhr_lastExtremum_gt f up hlt hahead
      have hkhi : k ≤ hi := by
        dsimp [k]
        exact hlhr_lastExtremum_le_hi f up (le_of_lt hlt)
      intro p hp
      simp only [hlhr_intervalsAux, hlt, ↓reduceIte, List.mem_cons] at hp
      rcases hp with rfl | hp
      · refine ⟨up, hklo, ?_, ?_⟩
        · intro j hjlo hjhi
          exact hahead j hjlo (le_trans hjhi hkhi)
        · intro j hjlo hjhi
          exact (hlhr_lastExtremum_spec f up (le_of_lt hlt)).2.2
            j hjlo (le_trans hjhi hkhi)
      · by_cases hk : k < hi
        · exact ih k (!up) hk (hlhr_ahead_next f up hlt) p hp
        · have hkeq : k = hi := by omega
          have htail : hlhr_intervalsAux f hi fuel (!up) k = [] := by
            rw [hkeq]
            cases fuel <;> simp [hlhr_intervalsAux]
          rw [htail] at hp
          simp at hp

theorem hlhd_interval_is_bridge (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    ∃ up, HLHRBridgeInterval (hlhd_height ts hleg) up p := by
  have hne : ts ≠ [] := by
    intro hempty
    simp [hlhd_intervals, hempty, hlhr_intervalsAux] at hp
  exact hlhr_intervalsAux_bridge (hlhd_height ts hleg) ts.length
    ts.length 0 true (List.length_pos_iff.mpr hne)
      (hlhd_halfSpace_ahead ts hleg hhalf) p hp


theorem hlhd_bridge_source_color (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) (hp2 : p.2 ≤ ts.length)
    {up : Bool} (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p) :
    (up = true ∧
        (hlhc_prefixCoord ts hleg.1 p.1).color = .black) ∨
      (up = false ∧
        (hlhc_prefixCoord ts hleg.1 p.1).color = .white) := by
  have hk : p.1 < ts.length := lt_of_lt_of_le hb.1 hp2
  obtain ⟨e, he⟩ := hlhc_prefixCoord_adjacent ts hleg p.1 hk
  have hstep := hb.2.1 (p.1 + 1) (Nat.lt_succ_self p.1)
    (Nat.succ_le_iff.mpr hb.1)
  have hcases := hlhd_neighbor_depth_cases
    (hlhc_prefixCoord ts hleg.1 p.1) e
  cases up with
  | false =>
      right
      refine ⟨rfl, ?_⟩
      simp only [hlhr_signed, Bool.false_eq_true, ↓reduceIte,
        hlhd_height, hlhd_depth] at hstep
      rw [← he] at hstep
      rcases hcases with hinc | hdec | hflat
      · rw [hinc.1] at hstep
        push_cast at hstep
        norm_num at hstep
      · exact hdec.2.1
      · rw [hflat.1] at hstep
        exact (lt_irrefl _ hstep).elim
  | true =>
      left
      refine ⟨rfl, ?_⟩
      simp only [hlhr_signed, ↓reduceIte, hlhd_height, hlhd_depth] at hstep
      rw [← he] at hstep
      rcases hcases with hinc | hdec | hflat
      · exact hinc.2.1
      · rw [hdec.1] at hstep
        push_cast at hstep
        linarith
      · rw [hflat.1] at hstep
        exact (lt_irrefl _ hstep).elim


theorem hlhd_bridge_depth_bounds (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (p : ℕ × ℕ) {up : Bool}
    (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p)
    {k : ℕ} (hklo : p.1 ≤ k) (hkhi : k ≤ p.2) :
    hlhr_signed up (hlhd_height ts hleg p.1) ≤
        hlhr_signed up (hlhd_height ts hleg k) ∧
      hlhr_signed up (hlhd_height ts hleg k) ≤
        hlhr_signed up (hlhd_height ts hleg p.2) := by
  constructor
  · rcases eq_or_lt_of_le hklo with rfl | hk
    · exact le_rfl
    · exact le_of_lt (hb.2.1 k hk hkhi)
  · exact hb.2.2 k hklo hkhi


theorem hlhd_interval_index_bounds (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    ∀ p ∈ hlhd_intervals ts hleg, p.1 < p.2 ∧ p.2 ≤ ts.length := by
  intro p hp
  have hne : ts ≠ [] := by
    intro hempty
    simp [hlhd_intervals, hempty, hlhr_intervalsAux] at hp
  exact hlhr_intervalsAux_bounds (hlhd_height ts hleg) ts.length
    ts.length 0 true (List.length_pos_iff.mpr hne)
      (hlhd_halfSpace_ahead ts hleg hhalf) p hp |>.2


end
end StatMech.Universality
