/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveVertexConnector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRawSimpleFromEdges
import Def.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveVertexConnector


namespace StatMech.FrontierA

open Set


@[simp] theorem kwHVConnectorCorner_re (a b : ℂ) :
    (kwHVConnectorCorner a b).re = b.re := by
  simp [kwHVConnectorCorner]

@[simp] theorem kwHVConnectorCorner_im (a b : ℂ) :
    (kwHVConnectorCorner a b).im = a.im := by
  simp [kwHVConnectorCorner]

@[simp] theorem kwVHConnectorCorner_re (a b : ℂ) :
    (kwVHConnectorCorner a b).re = a.re := by
  simp [kwVHConnectorCorner]

@[simp] theorem kwVHConnectorCorner_im (a b : ℂ) :
    (kwVHConnectorCorner a b).im = b.im := by
  simp [kwVHConnectorCorner]

theorem openSegment_same_im_disjoint_rayTail_left
    (a c : ℂ) (haIm : a.im ≠ 0) (him : c.im = a.im) :
    Disjoint {z : ℂ | Sbtw ℝ a z c} (kwOpenRayTail a) := by
  rw [Set.disjoint_left]
  rintro z hz ⟨t, ht, rfl⟩
  obtain ⟨s, hs, hline⟩ := hz.mem_image_Ioo
  have heq := congrArg Complex.im hline
  rw [AffineMap.lineMap_apply_module] at heq
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, him] at heq
  have htOne : t = 1 := by
    apply mul_right_cancel₀ haIm
    nlinarith
  linarith

theorem openSegment_same_re_disjoint_rayTail_left
    (a c : ℂ) (haRe : a.re ≠ 0) (hre : c.re = a.re) :
    Disjoint {z : ℂ | Sbtw ℝ a z c} (kwOpenRayTail a) := by
  rw [Set.disjoint_left]
  rintro z hz ⟨t, ht, rfl⟩
  obtain ⟨s, hs, hline⟩ := hz.mem_image_Ioo
  have heq := congrArg Complex.re hline
  rw [AffineMap.lineMap_apply_module] at heq
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, hre] at heq
  have htOne : t = 1 := by
    apply mul_right_cancel₀ haRe
    nlinarith
  linarith

theorem openSegment_same_im_disjoint_rayTail_right
    (c b : ℂ) (hbIm : b.im ≠ 0) (him : c.im = b.im) :
    Disjoint {z : ℂ | Sbtw ℝ c z b} (kwOpenRayTail b) := by
  convert openSegment_same_im_disjoint_rayTail_left b c hbIm him using 1
  ext z
  exact sbtw_comm

theorem openSegment_same_re_disjoint_rayTail_right
    (c b : ℂ) (hbRe : b.re ≠ 0) (hre : c.re = b.re) :
    Disjoint {z : ℂ | Sbtw ℝ c z b} (kwOpenRayTail b) := by
  convert openSegment_same_re_disjoint_rayTail_left b c hbRe hre using 1
  ext z
  exact sbtw_comm


theorem kwHVConnector_first_disjoint_leftRay
    (a b : ℂ) (haIm : a.im ≠ 0) :
    Disjoint {z : ℂ | Sbtw ℝ a z (kwHVConnectorCorner a b)}
      (kwOpenRayTail a) :=
  openSegment_same_im_disjoint_rayTail_left a
    (kwHVConnectorCorner a b) haIm (kwHVConnectorCorner_im a b)


theorem kwHVConnector_second_disjoint_rightRay
    (a b : ℂ) (hbRe : b.re ≠ 0) :
    Disjoint {z : ℂ | Sbtw ℝ (kwHVConnectorCorner a b) z b}
      (kwOpenRayTail b) :=
  openSegment_same_re_disjoint_rayTail_right
    (kwHVConnectorCorner a b) b hbRe (kwHVConnectorCorner_re a b)


theorem kwVHConnector_first_disjoint_leftRay
    (a b : ℂ) (haRe : a.re ≠ 0) :
    Disjoint {z : ℂ | Sbtw ℝ a z (kwVHConnectorCorner a b)}
      (kwOpenRayTail a) :=
  openSegment_same_re_disjoint_rayTail_left a
    (kwVHConnectorCorner a b) haRe (kwVHConnectorCorner_re a b)


theorem kwVHConnector_second_disjoint_rightRay
    (a b : ℂ) (hbIm : b.im ≠ 0) :
    Disjoint {z : ℂ | Sbtw ℝ (kwVHConnectorCorner a b) z b}
      (kwOpenRayTail b) :=
  openSegment_same_im_disjoint_rayTail_right
    (kwVHConnectorCorner a b) b hbIm (kwVHConnectorCorner_im a b)

theorem hvFirst_hit_rightRay_witness
    {a b : ℂ}
    (h : ¬Disjoint
      {z : ℂ | Sbtw ℝ a z (kwHVConnectorCorner a b)}
      (kwOpenRayTail b)) :
    ∃ t s : ℝ, 1 < t ∧ s ∈ Ioo (0 : ℝ) 1 ∧
      t * b.im = a.im ∧
      t * b.re = (1 - s) * a.re + s * b.re := by
  obtain ⟨z, hzseg, hzray⟩ := Set.not_disjoint_iff.mp h
  obtain ⟨t, ht, rfl⟩ := hzray
  obtain ⟨s, hs, hline⟩ := hzseg.mem_image_Ioo
  refine ⟨t, s, ht, hs, ?_, ?_⟩
  · have him := congrArg Complex.im hline
    rw [AffineMap.lineMap_apply_module] at him
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, kwHVConnectorCorner_im] at him
    linarith
  · have hre := congrArg Complex.re hline
    rw [AffineMap.lineMap_apply_module] at hre
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, kwHVConnectorCorner_re] at hre
    linarith

theorem hvSecond_hit_leftRay_witness
    {a b : ℂ}
    (h : ¬Disjoint
      {z : ℂ | Sbtw ℝ (kwHVConnectorCorner a b) z b}
      (kwOpenRayTail a)) :
    ∃ t s : ℝ, 1 < t ∧ s ∈ Ioo (0 : ℝ) 1 ∧
      t * a.re = b.re ∧
      t * a.im = (1 - s) * a.im + s * b.im := by
  obtain ⟨z, hzseg, hzray⟩ := Set.not_disjoint_iff.mp h
  obtain ⟨t, ht, rfl⟩ := hzray
  obtain ⟨s, hs, hline⟩ := hzseg.mem_image_Ioo
  refine ⟨t, s, ht, hs, ?_, ?_⟩
  · have hre := congrArg Complex.re hline
    rw [AffineMap.lineMap_apply_module] at hre
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, kwHVConnectorCorner_re] at hre
    linarith
  · have him := congrArg Complex.im hline
    rw [AffineMap.lineMap_apply_module] at him
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, kwHVConnectorCorner_im] at him
    linarith

theorem vhFirst_hit_rightRay_witness
    {a b : ℂ}
    (h : ¬Disjoint
      {z : ℂ | Sbtw ℝ a z (kwVHConnectorCorner a b)}
      (kwOpenRayTail b)) :
    ∃ t s : ℝ, 1 < t ∧ s ∈ Ioo (0 : ℝ) 1 ∧
      t * b.re = a.re ∧
      t * b.im = (1 - s) * a.im + s * b.im := by
  obtain ⟨z, hzseg, hzray⟩ := Set.not_disjoint_iff.mp h
  obtain ⟨t, ht, rfl⟩ := hzray
  obtain ⟨s, hs, hline⟩ := hzseg.mem_image_Ioo
  refine ⟨t, s, ht, hs, ?_, ?_⟩
  · have hre := congrArg Complex.re hline
    rw [AffineMap.lineMap_apply_module] at hre
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, kwVHConnectorCorner_re] at hre
    linarith
  · have him := congrArg Complex.im hline
    rw [AffineMap.lineMap_apply_module] at him
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, kwVHConnectorCorner_im] at him
    linarith

theorem vhSecond_hit_leftRay_witness
    {a b : ℂ}
    (h : ¬Disjoint
      {z : ℂ | Sbtw ℝ (kwVHConnectorCorner a b) z b}
      (kwOpenRayTail a)) :
    ∃ t s : ℝ, 1 < t ∧ s ∈ Ioo (0 : ℝ) 1 ∧
      t * a.im = b.im ∧
      t * a.re = (1 - s) * a.re + s * b.re := by
  obtain ⟨z, hzseg, hzray⟩ := Set.not_disjoint_iff.mp h
  obtain ⟨t, ht, rfl⟩ := hzray
  obtain ⟨s, hs, hline⟩ := hzseg.mem_image_Ioo
  refine ⟨t, s, ht, hs, ?_, ?_⟩
  · have him := congrArg Complex.im hline
    rw [AffineMap.lineMap_apply_module] at him
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, kwVHConnectorCorner_im] at him
    linarith
  · have hre := congrArg Complex.re hline
    rw [AffineMap.lineMap_apply_module] at hre
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, kwVHConnectorCorner_re] at hre
    linarith

theorem hvFirst_vhFirst_not_both_hit
    {a b : ℂ} (haRe : a.re ≠ 0) (hbIm : b.im ≠ 0)
    (hHV : ¬Disjoint
      {z : ℂ | Sbtw ℝ a z (kwHVConnectorCorner a b)}
      (kwOpenRayTail b))
    (hVH : ¬Disjoint
      {z : ℂ | Sbtw ℝ a z (kwVHConnectorCorner a b)}
      (kwOpenRayTail b)) : False := by
  obtain ⟨t, s, ht, hs, htIm, htRe⟩ := hvFirst_hit_rightRay_witness hHV
  obtain ⟨u, r, hu, hr, huRe, huIm⟩ := vhFirst_hit_rightRay_witness hVH
  have htrel : t = (1 - s) * u + s := by
    apply mul_right_cancel₀ haRe
    calc
      t * a.re = t * (u * b.re) := by rw [huRe]
      _ = u * (t * b.re) := by ring
      _ = u * ((1 - s) * a.re + s * b.re) := by rw [htRe]
      _ = ((1 - s) * u + s) * a.re := by rw [← huRe]; ring
  have hurel : u = (1 - r) * t + r := by
    apply mul_right_cancel₀ hbIm
    calc
      u * b.im = (1 - r) * a.im + r * b.im := huIm
      _ = (1 - r) * (t * b.im) + r * b.im := by rw [htIm]
      _ = ((1 - r) * t + r) * b.im := by ring
  nlinarith [hs.1, hs.2, hr.1, hr.2]

theorem hvFirst_vhSecond_not_both_hit
    {a b : ℂ} (hbIm : b.im ≠ 0)
    (hHV : ¬Disjoint
      {z : ℂ | Sbtw ℝ a z (kwHVConnectorCorner a b)}
      (kwOpenRayTail b))
    (hVH : ¬Disjoint
      {z : ℂ | Sbtw ℝ (kwVHConnectorCorner a b) z b}
      (kwOpenRayTail a)) : False := by
  obtain ⟨t, s, ht, hs, htIm, htRe⟩ := hvFirst_hit_rightRay_witness hHV
  obtain ⟨u, r, hu, hr, huIm, huRe⟩ := vhSecond_hit_leftRay_witness hVH
  have hprod : u * t = 1 := by
    apply mul_right_cancel₀ hbIm
    calc
      (u * t) * b.im = u * (t * b.im) := by ring
      _ = u * a.im := by rw [htIm]
      _ = b.im := huIm
      _ = 1 * b.im := by ring
  nlinarith

theorem hvSecond_vhFirst_not_both_hit
    {a b : ℂ} (hbRe : b.re ≠ 0)
    (hHV : ¬Disjoint
      {z : ℂ | Sbtw ℝ (kwHVConnectorCorner a b) z b}
      (kwOpenRayTail a))
    (hVH : ¬Disjoint
      {z : ℂ | Sbtw ℝ a z (kwVHConnectorCorner a b)}
      (kwOpenRayTail b)) : False := by
  obtain ⟨t, s, ht, hs, htRe, htIm⟩ := hvSecond_hit_leftRay_witness hHV
  obtain ⟨u, r, hu, hr, huRe, huIm⟩ := vhFirst_hit_rightRay_witness hVH
  have hprod : t * u = 1 := by
    apply mul_right_cancel₀ hbRe
    calc
      (t * u) * b.re = t * (u * b.re) := by ring
      _ = t * a.re := by rw [huRe]
      _ = b.re := htRe
      _ = 1 * b.re := by ring
  nlinarith

theorem hvSecond_vhSecond_not_both_hit
    {a b : ℂ} (haIm : a.im ≠ 0) (hbRe : b.re ≠ 0)
    (hHV : ¬Disjoint
      {z : ℂ | Sbtw ℝ (kwHVConnectorCorner a b) z b}
      (kwOpenRayTail a))
    (hVH : ¬Disjoint
      {z : ℂ | Sbtw ℝ (kwVHConnectorCorner a b) z b}
      (kwOpenRayTail a)) : False := by
  obtain ⟨t, s, ht, hs, htRe, htIm⟩ := hvSecond_hit_leftRay_witness hHV
  obtain ⟨u, r, hu, hr, huIm, huRe⟩ := vhSecond_hit_leftRay_witness hVH
  have htrel : t = (1 - s) + s * u := by
    apply mul_right_cancel₀ haIm
    calc
      t * a.im = (1 - s) * a.im + s * b.im := htIm
      _ = (1 - s) * a.im + s * (u * a.im) := by rw [huIm]
      _ = ((1 - s) + s * u) * a.im := by ring
  have hurel : u = (1 - r) + r * t := by
    apply mul_right_cancel₀ hbRe
    calc
      u * b.re = u * (t * a.re) := by rw [htRe]
      _ = t * (u * a.re) := by ring
      _ = t * ((1 - r) * a.re + r * b.re) := by rw [huRe]
      _ = ((1 - r) + r * t) * b.re := by rw [← htRe]; ring
  nlinarith [hs.1, hs.2, hr.1, hr.2]


theorem exists_adaptiveConnector_oppositeRay_disjoint
    (a b : ℂ)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0) :
    (Disjoint {z : ℂ | Sbtw ℝ a z (kwHVConnectorCorner a b)}
        (kwOpenRayTail b) ∧
      Disjoint {z : ℂ | Sbtw ℝ (kwHVConnectorCorner a b) z b}
        (kwOpenRayTail a)) ∨
    (Disjoint {z : ℂ | Sbtw ℝ a z (kwVHConnectorCorner a b)}
        (kwOpenRayTail b) ∧
      Disjoint {z : ℂ | Sbtw ℝ (kwVHConnectorCorner a b) z b}
        (kwOpenRayTail a)) := by
  classical
  by_cases hHVFirst : Disjoint
      {z : ℂ | Sbtw ℝ a z (kwHVConnectorCorner a b)}
      (kwOpenRayTail b)
  · by_cases hHVSecond : Disjoint
        {z : ℂ | Sbtw ℝ (kwHVConnectorCorner a b) z b}
        (kwOpenRayTail a)
    · exact Or.inl ⟨hHVFirst, hHVSecond⟩
    · right
      constructor
      · by_contra h
        exact hvSecond_vhFirst_not_both_hit hbRe hHVSecond h
      · by_contra h
        exact hvSecond_vhSecond_not_both_hit haIm hbRe hHVSecond h
  · by_cases hHVSecond : Disjoint
        {z : ℂ | Sbtw ℝ (kwHVConnectorCorner a b) z b}
        (kwOpenRayTail a)
    · right
      constructor
      · by_contra h
        exact hvFirst_vhFirst_not_both_hit haRe hbIm hHVFirst h
      · by_contra h
        exact hvFirst_vhSecond_not_both_hit hbIm hHVFirst h
    · right
      constructor
      · by_contra h
        exact hvFirst_vhFirst_not_both_hit haRe hbIm hHVFirst h
      · by_contra h
        exact hvSecond_vhSecond_not_both_hit haIm hbRe hHVSecond h


end StatMech.FrontierA
