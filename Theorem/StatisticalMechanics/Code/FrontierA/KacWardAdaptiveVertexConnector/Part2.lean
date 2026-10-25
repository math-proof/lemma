/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveVertexConnector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRawSimpleFromEdges
import Structure.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveVertexConnector


namespace StatMech.FrontierA

open Set


theorem hvConnector_turn_ne_zero
    {a b : ℂ} (hre : a.re ≠ b.re) (him : a.im ≠ b.im) :
    kwComplexCross (kwHVConnectorCorner a b - a)
      (b - kwHVConnectorCorner a b) ≠ 0 := by
  unfold kwHVConnectorCorner kwComplexCross
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  norm_num
  exact ⟨sub_ne_zero.mpr hre.symm, sub_ne_zero.mpr him.symm⟩

theorem vhConnector_turn_ne_zero
    {a b : ℂ} (hre : a.re ≠ b.re) (him : a.im ≠ b.im) :
    kwComplexCross (kwVHConnectorCorner a b - a)
      (b - kwVHConnectorCorner a b) ≠ 0 := by
  unfold kwVHConnectorCorner kwComplexCross
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  norm_num
  exact ⟨sub_ne_zero.mpr him.symm, sub_ne_zero.mpr hre.symm⟩


theorem exists_adaptiveConnectorData
    (a b : ℂ)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0)
    (hre : a.re ≠ b.re) (him : a.im ≠ b.im) :
    Nonempty (KWAdaptiveConnectorData a b) := by
  rcases exists_adaptiveConnector_oppositeRay_disjoint a b
      haRe haIm hbRe hbIm with hHV | hVH
  · refine ⟨⟨kwHVConnectorCorner a b, Or.inl rfl, ?_, ?_,
      hvConnector_turn_ne_zero hre him, ?_⟩⟩
    · intro h
      have := congrArg Complex.re h
      simp only [kwHVConnectorCorner_re] at this
      exact hre this.symm
    · intro h
      have := congrArg Complex.im h
      simp only [kwHVConnectorCorner_im] at this
      exact him this
    · apply Disjoint.union_left
      · apply Disjoint.union_right
        · exact kwHVConnector_first_disjoint_leftRay a b haIm
        · exact hHV.1
      · apply Disjoint.union_right
        · exact hHV.2
        · exact kwHVConnector_second_disjoint_rightRay a b hbRe
  · refine ⟨⟨kwVHConnectorCorner a b, Or.inr rfl, ?_, ?_,
      vhConnector_turn_ne_zero hre him, ?_⟩⟩
    · intro h
      have := congrArg Complex.im h
      simp only [kwVHConnectorCorner_im] at this
      exact him this.symm
    · intro h
      have := congrArg Complex.re h
      simp only [kwVHConnectorCorner_re] at this
      exact hre this
    · apply Disjoint.union_left
      · apply Disjoint.union_right
        · exact kwVHConnector_first_disjoint_leftRay a b haRe
        · exact hVH.1
      · apply Disjoint.union_right
        · exact hVH.2
        · exact kwVHConnector_second_disjoint_rightRay a b hbIm


theorem exists_bounded_incomingScale_both_extents_lt
    (a b : ℂ) (beta cap : ℝ) (hbeta : 0 < beta) (hcap : 0 < cap)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < cap ∧
      |alpha * a.re| < |beta * b.re| ∧
      |alpha * a.im| < |beta * b.im| := by
  obtain ⟨alphaRe, hRePos, hReCap, hRe⟩ :=
    exists_bounded_incomingScale_horizontal_extent_lt
      a b beta cap hbeta hcap haRe hbRe
  obtain ⟨alphaIm, hImPos, hImCap, hIm⟩ :=
    exists_bounded_incomingScale_horizontal_extent_lt
      (a.im : ℂ) (b.im : ℂ) beta cap hbeta hcap
      (by simpa using haIm) (by simpa using hbIm)
  let alpha := min alphaRe alphaIm
  have halpha : 0 < alpha := lt_min hRePos hImPos
  refine ⟨alpha, halpha, (min_le_left _ _).trans_lt hReCap, ?_, ?_⟩
  · calc
      |alpha * a.re| = alpha * |a.re| := by
        rw [abs_mul, abs_of_pos halpha]
      _ ≤ alphaRe * |a.re| :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)
      _ = |alphaRe * a.re| := by
        rw [abs_mul, abs_of_pos hRePos]
      _ < |beta * b.re| := hRe
  · have hIm' : |alphaIm * a.im| < |beta * b.im| := by
      simpa only [Complex.ofReal_re] using hIm
    calc
      |alpha * a.im| = alpha * |a.im| := by
        rw [abs_mul, abs_of_pos halpha]
      _ ≤ alphaIm * |a.im| :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _)
      _ = |alphaIm * a.im| := by
        rw [abs_mul, abs_of_pos hImPos]
      _ < |beta * b.im| := hIm'


theorem KWFiniteSimplePolygon.exists_adaptiveConnectorScales
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (beta cap : ℝ) (hbeta : 0 < beta) (hcap : 0 < cap) :
    ∃ alpha : Fin n → ℝ,
      (∀ i : Fin n, 0 < alpha i ∧ alpha i < cap ∧
        |alpha i * (-polygon.edgeVector (i - 1)).re| <
          |beta * (polygon.edgeVector i).re| ∧
        |alpha i * (-polygon.edgeVector (i - 1)).im| <
          |beta * (polygon.edgeVector i).im|) ∧
      ∀ i : Fin n, Nonempty (KWAdaptiveConnectorData
        (alpha i * (-polygon.edgeVector (i - 1)))
        (beta * polygon.edgeVector i)) := by
  have hincomingRe (i : Fin n) :
      (-polygon.edgeVector (i - 1)).re ≠ 0 := by
    rw [Complex.neg_re]
    exact neg_ne_zero.mpr (hcoords (i - 1)).1
  have hincomingIm (i : Fin n) :
      (-polygon.edgeVector (i - 1)).im ≠ 0 := by
    rw [Complex.neg_im]
    exact neg_ne_zero.mpr (hcoords (i - 1)).2
  choose alpha halpha using fun i : Fin n ↦
    exists_bounded_incomingScale_both_extents_lt
      (-polygon.edgeVector (i - 1)) (polygon.edgeVector i)
      beta cap hbeta hcap (hincomingRe i) (hincomingIm i)
        (hcoords i).1 (hcoords i).2
  refine ⟨alpha, halpha, ?_⟩
  intro i
  let a : ℂ := alpha i * (-polygon.edgeVector (i - 1))
  let b : ℂ := beta * polygon.edgeVector i
  have haRe : a.re ≠ 0 := by
    dsimp only [a]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_ne_zero (halpha i).1.ne' (hincomingRe i)
  have haIm : a.im ≠ 0 := by
    dsimp only [a]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    exact mul_ne_zero (halpha i).1.ne' (hincomingIm i)
  have hbRe : b.re ≠ 0 := by
    dsimp only [b]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_ne_zero hbeta.ne' (hcoords i).1
  have hbIm : b.im ≠ 0 := by
    dsimp only [b]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    exact mul_ne_zero hbeta.ne' (hcoords i).2
  have hre : a.re ≠ b.re := by
    intro heq
    have habs := congrArg abs heq
    have hlt := (halpha i).2.2.1
    dsimp only [a, b] at habs
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at habs
    exact (ne_of_lt hlt) habs
  have him : a.im ≠ b.im := by
    intro heq
    have habs := congrArg abs heq
    have hlt := (halpha i).2.2.2
    dsimp only [a, b] at habs
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] at habs
    exact (ne_of_lt hlt) habs
  exact exists_adaptiveConnectorData a b haRe haIm hbRe hbIm hre him

end StatMech.FrontierA
