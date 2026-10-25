/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIncidentStairPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAxisStaircase.Part2


namespace StatMech.FrontierA

open Set

theorem mul_sub_pos_of_abs_lt_abs {x y : ℝ} (h : |x| < |y|) :
    0 < y * (y - x) := by
  have hy : y ≠ 0 := by
    intro hy
    rw [hy, abs_zero] at h
    exact (not_lt_of_ge (abs_nonneg x)) h
  rcases lt_or_gt_of_ne hy with hyneg | hypos
  · have hyx : y < x := by
      have hbelow : y < -|x| := by
        rw [abs_of_neg hyneg] at h
        linarith
      exact hbelow.trans_le (neg_abs_le x)
    exact mul_pos_of_neg_of_neg hyneg (sub_neg.mpr hyx)
  · have hxy : x < y := by
      calc
        x ≤ |x| := le_abs_self x
        _ < |y| := h
        _ = y := abs_of_pos hypos
    exact mul_pos hypos (sub_pos.mpr hxy)


theorem exists_incomingScale_horizontal_extent_lt
    (a b : ℂ) (beta : ℝ) (hbeta : 0 < beta)
    (haRe : a.re ≠ 0) (hbRe : b.re ≠ 0) :
    ∃ alpha : ℝ, 0 < alpha ∧
      |alpha * a.re| < |beta * b.re| := by
  let alpha := beta * |b.re| / (2 * |a.re|)
  have haAbs : 0 < |a.re| := abs_pos.mpr haRe
  have hbAbs : 0 < |b.re| := abs_pos.mpr hbRe
  have halpha : 0 < alpha := by
    dsimp only [alpha]
    positivity
  refine ⟨alpha, halpha, ?_⟩
  rw [abs_mul, abs_mul, abs_of_pos halpha, abs_of_pos hbeta]
  dsimp only [alpha]
  rw [div_mul_eq_mul_div, mul_div_assoc]
  field_simp
  nlinarith

theorem exists_bounded_incomingScale_horizontal_extent_lt
    (a b : ℂ) (beta cap : ℝ) (hbeta : 0 < beta) (hcap : 0 < cap)
    (haRe : a.re ≠ 0) (hbRe : b.re ≠ 0) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < cap ∧
      |alpha * a.re| < |beta * b.re| := by
  obtain ⟨alphaZero, halphaZero, hextent⟩ :=
    exists_incomingScale_horizontal_extent_lt a b beta hbeta haRe hbRe
  let alpha := min alphaZero (cap / 2)
  have halpha : 0 < alpha := by
    exact lt_min halphaZero (half_pos hcap)
  refine ⟨alpha, halpha, ?_, ?_⟩
  · exact (min_le_right _ _).trans_lt (by linarith)
  · calc
      |alpha * a.re| = alpha * |a.re| := by
        rw [abs_mul, abs_of_pos halpha]
      _ ≤ alphaZero * |a.re| := by
        exact mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)
      _ = |alphaZero * a.re| := by
        rw [abs_mul, abs_of_pos halphaZero]
      _ < |beta * b.re| := hextent


theorem KWFiniteSimplePolygon.exists_incidentPatchScales
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (beta cap : ℝ) (hbeta : 0 < beta) (hcap : 0 < cap) :
    ∃ alpha : Fin n → ℝ, ∀ i : Fin n,
      0 < alpha i ∧ alpha i < cap ∧
      |alpha i * (-polygon.edgeVector (i - 1)).re| <
        |beta * (polygon.edgeVector i).re| := by
  have hincomingRe (i : Fin n) :
      (-polygon.edgeVector (i - 1)).re ≠ 0 := by
    rw [Complex.neg_re]
    exact neg_ne_zero.mpr (hcoords (i - 1)).1
  choose alpha halpha using fun i : Fin n ↦
    exists_bounded_incomingScale_horizontal_extent_lt
      (-polygon.edgeVector (i - 1)) (polygon.edgeVector i)
      beta cap hbeta hcap (hincomingRe i) (hcoords i).1
  exact ⟨alpha, halpha⟩


end StatMech.FrontierA
