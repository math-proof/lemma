/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIncidentStairPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAxisStaircase.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardIncidentStairPatch


namespace StatMech.FrontierA

open Set

theorem kw_incidentPatch_incomingHorizontal_disjoint_outgoingVertical
    (v a b : ℂ) (alpha beta : ℝ)
    (hbeta : 0 < beta) (hbIm : b.im ≠ 0)
    (hextent : |alpha * a.re| < |beta * b.re|) :
    Disjoint
      {z : ℂ | Sbtw ℝ (kwIncomingPatchBase v a alpha) z
        (kwIncomingPatchCorner v a alpha)}
      {z : ℂ | Sbtw ℝ (kwOutgoingPatchCorner v b beta) z
        (kwOutgoingPatchEnd v b beta)} := by
  let incomingBase := kwIncomingPatchBase v a alpha
  let incomingCorner := kwIncomingPatchCorner v a alpha
  let outgoingCorner := kwOutgoingPatchCorner v b beta
  let outgoingEnd := kwOutgoingPatchEnd v b beta
  let firstCross := kwComplexCross (outgoingEnd - outgoingCorner)
    (incomingBase - outgoingCorner)
  let secondCross := kwComplexCross (outgoingEnd - outgoingCorner)
    (incomingCorner - outgoingCorner)
  have hhorizontal : 0 < (beta * b.re) *
      (beta * b.re - alpha * a.re) :=
    mul_sub_pos_of_abs_lt_abs hextent
  have hvertical : 0 < (beta * b.im) ^ 2 := by
    rw [pow_two]
    exact mul_self_pos.mpr (mul_ne_zero hbeta.ne' hbIm)
  have hproduct : 0 < firstCross * secondCross := by
    have hfactor : firstCross * secondCross =
        (beta * b.im) ^ 2 *
          ((beta * b.re) * (beta * b.re - alpha * a.re)) := by
      dsimp only [firstCross, secondCross, incomingBase, incomingCorner,
        outgoingCorner, outgoingEnd, kwIncomingPatchBase,
        kwIncomingPatchCorner, kwOutgoingPatchCorner, kwOutgoingPatchEnd]
      unfold kwHorizontalPart kwVerticalPart kwComplexCross
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [hfactor]
    exact mul_pos hvertical hhorizontal
  exact (kw_openSegments_disjoint_of_cross_same_sign
    (mul_pos_iff.mp hproduct)).symm

theorem kw_incidentPatch_incomingHorizontal_disjoint_outgoingHorizontal
    (v a b : ℂ) (alpha beta : ℝ)
    (halpha : 0 < alpha) (haRe : a.re ≠ 0) (haIm : a.im ≠ 0) :
    Disjoint
      {z : ℂ | Sbtw ℝ (kwIncomingPatchBase v a alpha) z
        (kwIncomingPatchCorner v a alpha)}
      {z : ℂ | Sbtw ℝ v z (kwOutgoingPatchCorner v b beta)} := by
  let c := kwComplexCross
    (kwIncomingPatchCorner v a alpha - kwIncomingPatchBase v a alpha)
    (v - kwIncomingPatchBase v a alpha)
  have heq : kwComplexCross
      (kwIncomingPatchCorner v a alpha - kwIncomingPatchBase v a alpha)
      (kwOutgoingPatchCorner v b beta - kwIncomingPatchBase v a alpha) = c := by
    dsimp only [c, kwIncomingPatchBase, kwIncomingPatchCorner,
      kwOutgoingPatchCorner]
    unfold kwHorizontalPart kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hc : c ≠ 0 := by
    dsimp only [c, kwIncomingPatchBase, kwIncomingPatchCorner]
    unfold kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf
    positivity
  apply kw_openSegments_disjoint_of_cross_same_sign
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · exact Or.inr ⟨hcneg, by rwa [heq]⟩
  · exact Or.inl ⟨hcpos, by rwa [heq]⟩

theorem kw_incidentPatch_incomingVertical_disjoint_outgoingVertical
    (v a b : ℂ) (alpha beta : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (haIm : a.im ≠ 0) (hbRe : b.re ≠ 0) :
    Disjoint
      {z : ℂ | Sbtw ℝ (kwIncomingPatchCorner v a alpha) z v}
      {z : ℂ | Sbtw ℝ (kwOutgoingPatchCorner v b beta) z
        (kwOutgoingPatchEnd v b beta)} := by
  let c := kwComplexCross
    (v - kwIncomingPatchCorner v a alpha)
    (kwOutgoingPatchCorner v b beta - kwIncomingPatchCorner v a alpha)
  have heq : kwComplexCross
      (v - kwIncomingPatchCorner v a alpha)
      (kwOutgoingPatchEnd v b beta - kwIncomingPatchCorner v a alpha) = c := by
    dsimp only [c, kwIncomingPatchCorner, kwOutgoingPatchCorner,
      kwOutgoingPatchEnd]
    unfold kwHorizontalPart kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hc : c ≠ 0 := by
    dsimp only [c, kwIncomingPatchCorner, kwOutgoingPatchCorner]
    unfold kwHorizontalPart kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf
    positivity
  apply kw_openSegments_disjoint_of_cross_same_sign
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · exact Or.inr ⟨hcneg, by rwa [heq]⟩
  · exact Or.inl ⟨hcpos, by rwa [heq]⟩

theorem kw_incidentPatch_incomingVertical_disjoint_outgoingHorizontal
    (v a b : ℂ) (alpha beta : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (haIm : a.im ≠ 0) (hbRe : b.re ≠ 0) :
    Disjoint
      {z : ℂ | Sbtw ℝ (kwIncomingPatchCorner v a alpha) z v}
      {z : ℂ | Sbtw ℝ v z (kwOutgoingPatchCorner v b beta)} := by
  rw [Set.disjoint_left]
  intro z hzin hzout
  have hcross : kwComplexCross
      (kwIncomingPatchCorner v a alpha - v)
      (kwOutgoingPatchCorner v b beta - v) ≠ 0 := by
    dsimp only [kwIncomingPatchCorner, kwOutgoingPatchCorner]
    unfold kwHorizontalPart kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf
    exact neg_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (mul_ne_zero halpha.ne' haIm)
        hbeta.ne') hbRe)
  exact Set.disjoint_left.mp
    (kw_openSegments_disjoint_of_common_left_cross_ne hcross)
    ((sbtw_comm).mpr hzin) hzout

theorem kw_incidentPatch_incomingHorizontal_closed_disjoint_outgoingVertical
    (v a b : ℂ) (alpha beta : ℝ)
    (hbeta : 0 < beta) (hbIm : b.im ≠ 0)
    (hextent : |alpha * a.re| < |beta * b.re|) :
    Disjoint
      (segment ℝ (kwIncomingPatchBase v a alpha)
        (kwIncomingPatchCorner v a alpha))
      (segment ℝ (kwOutgoingPatchCorner v b beta)
        (kwOutgoingPatchEnd v b beta)) := by
  let incomingBase := kwIncomingPatchBase v a alpha
  let incomingCorner := kwIncomingPatchCorner v a alpha
  let outgoingCorner := kwOutgoingPatchCorner v b beta
  let outgoingEnd := kwOutgoingPatchEnd v b beta
  let firstCross := kwComplexCross (outgoingEnd - outgoingCorner)
    (incomingBase - outgoingCorner)
  let secondCross := kwComplexCross (outgoingEnd - outgoingCorner)
    (incomingCorner - outgoingCorner)
  have hhorizontal : 0 < (beta * b.re) *
      (beta * b.re - alpha * a.re) :=
    mul_sub_pos_of_abs_lt_abs hextent
  have hvertical : 0 < (beta * b.im) ^ 2 := by
    rw [pow_two]
    exact mul_self_pos.mpr (mul_ne_zero hbeta.ne' hbIm)
  have hproduct : 0 < firstCross * secondCross := by
    have hfactor : firstCross * secondCross =
        (beta * b.im) ^ 2 *
          ((beta * b.re) * (beta * b.re - alpha * a.re)) := by
      dsimp only [firstCross, secondCross, incomingBase, incomingCorner,
        outgoingCorner, outgoingEnd, kwIncomingPatchBase,
        kwIncomingPatchCorner, kwOutgoingPatchCorner, kwOutgoingPatchEnd]
      unfold kwHorizontalPart kwVerticalPart kwComplexCross
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [hfactor]
    exact mul_pos hvertical hhorizontal
  exact (kw_segments_disjoint_of_cross_same_sign
    (mul_pos_iff.mp hproduct)).symm

theorem kw_incidentPatch_incomingHorizontal_closed_disjoint_outgoingHorizontal
    (v a b : ℂ) (alpha beta : ℝ)
    (halpha : 0 < alpha) (haRe : a.re ≠ 0) (haIm : a.im ≠ 0) :
    Disjoint
      (segment ℝ (kwIncomingPatchBase v a alpha)
        (kwIncomingPatchCorner v a alpha))
      (segment ℝ v (kwOutgoingPatchCorner v b beta)) := by
  let c := kwComplexCross
    (kwIncomingPatchCorner v a alpha - kwIncomingPatchBase v a alpha)
    (v - kwIncomingPatchBase v a alpha)
  have heq : kwComplexCross
      (kwIncomingPatchCorner v a alpha - kwIncomingPatchBase v a alpha)
      (kwOutgoingPatchCorner v b beta - kwIncomingPatchBase v a alpha) = c := by
    dsimp only [c, kwIncomingPatchBase, kwIncomingPatchCorner,
      kwOutgoingPatchCorner]
    unfold kwHorizontalPart kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hc : c ≠ 0 := by
    dsimp only [c, kwIncomingPatchBase, kwIncomingPatchCorner]
    unfold kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf
    positivity
  apply kw_segments_disjoint_of_cross_same_sign
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · exact Or.inr ⟨hcneg, by rwa [heq]⟩
  · exact Or.inl ⟨hcpos, by rwa [heq]⟩

theorem kw_incidentPatch_incomingVertical_closed_disjoint_outgoingVertical
    (v a b : ℂ) (alpha beta : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (haIm : a.im ≠ 0) (hbRe : b.re ≠ 0) :
    Disjoint
      (segment ℝ (kwIncomingPatchCorner v a alpha) v)
      (segment ℝ (kwOutgoingPatchCorner v b beta)
        (kwOutgoingPatchEnd v b beta)) := by
  let c := kwComplexCross
    (v - kwIncomingPatchCorner v a alpha)
    (kwOutgoingPatchCorner v b beta - kwIncomingPatchCorner v a alpha)
  have heq : kwComplexCross
      (v - kwIncomingPatchCorner v a alpha)
      (kwOutgoingPatchEnd v b beta - kwIncomingPatchCorner v a alpha) = c := by
    dsimp only [c, kwIncomingPatchCorner, kwOutgoingPatchCorner,
      kwOutgoingPatchEnd]
    unfold kwHorizontalPart kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hc : c ≠ 0 := by
    dsimp only [c, kwIncomingPatchCorner, kwOutgoingPatchCorner]
    unfold kwHorizontalPart kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf
    positivity
  apply kw_segments_disjoint_of_cross_same_sign
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · exact Or.inr ⟨hcneg, by rwa [heq]⟩
  · exact Or.inl ⟨hcpos, by rwa [heq]⟩


theorem kw_incidentPatch_pairwise_disjoint
    (v a b : ℂ) (alpha beta : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0)
    (hextent : |alpha * a.re| < |beta * b.re|) :
    Disjoint
      ({z : ℂ | Sbtw ℝ (kwIncomingPatchBase v a alpha) z
          (kwIncomingPatchCorner v a alpha)} ∪
        {z : ℂ | Sbtw ℝ (kwIncomingPatchCorner v a alpha) z v})
      ({z : ℂ | Sbtw ℝ v z (kwOutgoingPatchCorner v b beta)} ∪
        {z : ℂ | Sbtw ℝ (kwOutgoingPatchCorner v b beta) z
          (kwOutgoingPatchEnd v b beta)}) := by
  rw [Set.disjoint_left]
  intro z hzin hzout
  rcases hzin with hzin | hzin <;> rcases hzout with hzout | hzout
  · exact Set.disjoint_left.mp
      (kw_incidentPatch_incomingHorizontal_disjoint_outgoingHorizontal
        v a b alpha beta halpha haRe haIm) hzin hzout
  · exact Set.disjoint_left.mp
      (kw_incidentPatch_incomingHorizontal_disjoint_outgoingVertical
        v a b alpha beta hbeta hbIm hextent) hzin hzout
  · exact Set.disjoint_left.mp
      (kw_incidentPatch_incomingVertical_disjoint_outgoingHorizontal
        v a b alpha beta halpha hbeta haIm hbRe) hzin hzout
  · exact Set.disjoint_left.mp
      (kw_incidentPatch_incomingVertical_disjoint_outgoingVertical
        v a b alpha beta halpha hbeta haIm hbRe) hzin hzout

end StatMech.FrontierA
