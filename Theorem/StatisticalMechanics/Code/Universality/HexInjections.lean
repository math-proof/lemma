/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Def.StatisticalMechanics.Code.Universality.HexInjections


namespace StatMech.Universality

open Complex

open scoped BigOperators


theorem hexSAWwt_nonneg (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) (ts : List ℤ) :
    0 ≤ hexSAWwt a h0 x ts := by
  unfold hexSAWwt
  split <;> positivity


theorem hexSAWwt_of_isLegalSAW (a : ℂ) (h0 : ℤ) (x : ℝ) {ts : List ℤ}
    (h : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
    hexSAWwt a h0 x ts = x ^ (HexWalk.ofTurns a h0 ts).numVertices := by
  unfold hexSAWwt
  rw [if_pos h]


theorem hexHalfStep_re_abs (h : ℤ) : |(HexWalk.halfStep h).re| ≤ 1 / 2 := by
  unfold HexWalk.halfStep
  rw [Complex.mul_re]
  have hb : |(hexUnit h).re| ≤ 1 :=
    le_trans (Complex.abs_re_le_norm _) (le_of_eq (norm_hexUnit h))
  simp only [show ((1 : ℂ) / 2).re = 1 / 2 by norm_num,
    show ((1 : ℂ) / 2).im = 0 by norm_num]
  rw [abs_le] at hb ⊢
  constructor <;> nlinarith [hb.1, hb.2]


theorem hexVerticesAux_re_le (m : ℂ) (h : ℤ) (ts : List ℤ) :
    ∀ v ∈ HexWalk.verticesAux m h ts, v.re ≤ m.re + (ts.length + 1 : ℝ) := by
  induction ts generalizing m h with
  | nil =>
    intro v hv
    rw [HexWalk.verticesAux_nil] at hv
    simp only [List.mem_singleton] at hv
    subst hv
    have hh := hexHalfStep_re_abs h
    rw [abs_le] at hh
    simp only [Complex.add_re, List.length_nil]
    push_cast
    nlinarith [hh.1, hh.2]
  | cons t ts ih =>
    intro v hv
    rw [HexWalk.verticesAux_cons] at hv
    simp only [List.mem_cons] at hv
    rcases hv with hv | hv
    · subst hv
      have hh := hexHalfStep_re_abs h
      rw [abs_le] at hh
      simp only [Complex.add_re, List.length_cons]
      push_cast
      nlinarith [hh.1, hh.2]
    · have hih := ih (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t) v hv
      have b1 := hexHalfStep_re_abs h
      have b2 := hexHalfStep_re_abs (h + t)
      rw [abs_le] at b1 b2
      simp only [Complex.add_re, List.length_cons] at hih ⊢
      push_cast at hih ⊢
      nlinarith [hih, b1.1, b1.2, b2.1, b2.2]


theorem hexReachWidth_len_ge (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ)
    (hreach : ∃ v ∈ (HexWalk.ofTurns a h0 ts).vertices, a.re + T ≤ v.re) :
    T ≤ (HexWalk.ofTurns a h0 ts).numVertices := by
  obtain ⟨v, hv, hge⟩ := hreach
  
  have hle : v.re ≤ a.re + (ts.length + 1 : ℝ) := by
    have := hexVerticesAux_re_le a h0 ts v
    simpa [HexWalk.vertices, HexWalk.ofTurns] using this hv
  
  have : (T : ℝ) ≤ (ts.length + 1 : ℝ) := by linarith
  have hnat : T ≤ ts.length + 1 := by exact_mod_cast this
  simpa [HexWalk.numVertices, HexWalk.ofTurns] using hnat


end StatMech.Universality
