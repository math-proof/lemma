/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum


namespace StatMech.Universality

open Complex

open HexWalk


theorem loopReverse_sum (L : List ℤ) : (loopReverse L).sum = - L.sum := by
  unfold loopReverse
  rw [List.sum_reverse]
  induction L with
  | nil => simp
  | cons x xs ih => simp [ih]; ring


@[simp]
theorem loopReverse_length (L : List ℤ) : (loopReverse L).length = L.length := by
  simp [loopReverse]


theorem loopReverse_legal (L : List ℤ) (hL : ∀ t ∈ L, t = 1 ∨ t = -1) :
    ∀ t ∈ loopReverse L, t = 1 ∨ t = -1 := by
  intro t ht
  unfold loopReverse at ht
  rw [List.mem_reverse, List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  rcases hL s hs with h | h <;> simp [h]


theorem loopReverse_involutive (L : List ℤ) : loopReverse (loopReverse L) = L := by
  unfold loopReverse
  rw [List.map_reverse, List.reverse_reverse, List.map_map]
  simp


theorem genuine_pair_zero_via_reversal (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (base Lq : List ℤ) (hLqsum : Lq.sum = -4)
    (hq : (ofTurns a h0 (base ++ Lq)).IsLegalSAW
        ∧ (ofTurns a h0 (base ++ Lq)).StaysIn region
        ∧ (ofTurns a h0 (base ++ Lq)).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (base ++ loopReverse Lq)).IsLegalSAW
        ∧ (ofTurns a h0 (base ++ loopReverse Lq)).StaysIn region
        ∧ (ofTurns a h0 (base ++ loopReverse Lq)).EndsAt (v + hexOmega ^ 2 * du)) :
    ((v + hexOmega * du) - v)
        * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (base ++ Lq)
      + ((v + hexOmega ^ 2 * du) - v)
          * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi
              (base ++ loopReverse Lq)
      = 0 :=
  genuine_pair_zero region a h0 v du base Lq (loopReverse Lq) hLqsum
    (by rw [loopReverse_sum, hLqsum]; ring) (loopReverse_length Lq).symm hq hr


theorem hexOmega_primRoot : IsPrimitiveRoot hexOmega 3 := by
  have h : hexOmega = Complex.exp (2 * Real.pi * Complex.I / 3) := by
    unfold hexOmega; congr 1; push_cast; ring
  rw [h]; exact Complex.isPrimitiveRoot_exp 3 (by norm_num)

theorem hexOmega_ne_one : hexOmega ≠ 1 := by
  intro h
  have := hexOmega_primRoot.pow_ne_one_of_pos_of_lt (l := 1) (by norm_num) (by norm_num)
  simp at this; exact this h

theorem hexOmega_sq_ne_one : hexOmega ^ 2 ≠ 1 :=
  hexOmega_primRoot.pow_ne_one_of_pos_of_lt (l := 2) (by norm_num) (by norm_num)

theorem hexOmega_ne_sq : hexOmega ≠ hexOmega ^ 2 := by
  intro h
  have hne : hexOmega ≠ 0 := hexOmega_primRoot.ne_zero (by norm_num)
  apply hexOmega_ne_one
  have h2 : hexOmega * hexOmega = hexOmega * 1 := by rw [mul_one, ← sq, ← h]
  exact mul_left_cancel₀ hne h2


theorem hexMid_p_ne_q {v du : ℂ} (hdu : du ≠ 0) : v + du ≠ v + hexOmega * du := by
  intro h
  have : du = hexOmega * du := by linear_combination h
  apply hexOmega_ne_one
  have := mul_right_cancel₀ hdu (by rw [one_mul]; exact this : (1 : ℂ) * du = hexOmega * du)
  exact this.symm


theorem hexMid_p_ne_r {v du : ℂ} (hdu : du ≠ 0) : v + du ≠ v + hexOmega ^ 2 * du := by
  intro h
  have : du = hexOmega ^ 2 * du := by linear_combination h
  apply hexOmega_sq_ne_one
  have := mul_right_cancel₀ hdu (by rw [one_mul]; exact this : (1 : ℂ) * du = hexOmega ^ 2 * du)
  exact this.symm


theorem hexMid_q_ne_r {v du : ℂ} (hdu : du ≠ 0) :
    v + hexOmega * du ≠ v + hexOmega ^ 2 * du := by
  intro h
  have hh : hexOmega * du = hexOmega ^ 2 * du := by linear_combination h
  apply hexOmega_ne_sq
  exact mul_right_cancel₀ hdu hh


theorem parafSummand_eq_zero_of_not_endsAt (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (z : ℂ) (σ x : ℝ) (ts : List ℤ) (hne : ¬ (ofTurns a h0 ts).EndsAt z) :
    parafSummand region a h0 z σ x ts = 0 := by
  unfold parafSummand
  rw [if_neg]
  rintro ⟨_, _, h⟩
  exact hne h


end StatMech.Universality
