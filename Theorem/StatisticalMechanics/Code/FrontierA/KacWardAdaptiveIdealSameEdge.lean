/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealSameEdge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveConnectorClosedSeparation


namespace StatMech.FrontierA

open Set

theorem lineMap_segment_point
    {a b : ℂ} {s t : ℝ} (hst : s ≤ t) {z : ℂ}
    (hz : z ∈ segment ℝ (AffineMap.lineMap a b s)
      (AffineMap.lineMap a b t)) :
    ∃ u ∈ Icc s t, z = AffineMap.lineMap a b u := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  let u := (1 - r) * s + r * t
  refine ⟨u, ?_, ?_⟩
  · constructor <;> dsimp only [u] <;> nlinarith [hr.1, hr.2]
  · simp only [AffineMap.lineMap_apply_module, Complex.real_smul]
    dsimp only [u]
    push_cast
    ring

theorem lineMap_parameterSegments_disjoint
    {a b : ℂ} (hab : a ≠ b)
    {s t u v : ℝ} (hst : s ≤ t) (huv : u ≤ v) (htu : t < u) :
    Disjoint
      (segment ℝ (AffineMap.lineMap a b s) (AffineMap.lineMap a b t))
      (segment ℝ (AffineMap.lineMap a b u) (AffineMap.lineMap a b v)) := by
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  obtain ⟨x, hx, hxz⟩ := lineMap_segment_point hst hz₁
  obtain ⟨y, hy, hyz⟩ := lineMap_segment_point huv hz₂
  have hxy : x = y := AffineMap.lineMap_injective ℝ hab (hxz.symm.trans hyz)
  rw [hxy] at hx
  linarith [hx.2, hy.1]

theorem lineMap_parameterSegments_disjoint_rev
    {a b : ℂ} (hab : a ≠ b)
    {s t u v : ℝ} (hst : s ≤ t) (huv : u ≤ v) (hvs : v < s) :
    Disjoint
      (segment ℝ (AffineMap.lineMap a b s) (AffineMap.lineMap a b t))
      (segment ℝ (AffineMap.lineMap a b u) (AffineMap.lineMap a b v)) := by
  exact (lineMap_parameterSegments_disjoint hab huv hst hvs).symm

end StatMech.FrontierA
