/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGenericPolygonReduction
import Def.StatisticalMechanics.Code.FrontierA.KacWardPolygonPerturbation


namespace StatMech.FrontierA

open scoped Convex

open Set

theorem dist_lineMap_le_of_endpoint_dist_le
    {a b a' b' : ℂ} {t eps : ℝ} (ht : t ∈ Icc 0 1)
    (ha : dist a' a ≤ eps) (hb : dist b' b ≤ eps) :
    dist (AffineMap.lineMap a' b' t) (AffineMap.lineMap a b t) ≤ eps := by
  rw [dist_eq_norm, AffineMap.lineMap_apply_module,
    AffineMap.lineMap_apply_module]
  have heq : (1 - t) • a' + t • b' - ((1 - t) • a + t • b) =
      (1 - t) • (a' - a) + t • (b' - b) := by
    module
  rw [heq]
  calc
    ‖(1 - t) • (a' - a) + t • (b' - b)‖ ≤
        ‖(1 - t) • (a' - a)‖ + ‖t • (b' - b)‖ := norm_add_le _ _
    _ = (1 - t) * dist a' a + t * dist b' b := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ht.1, abs_of_nonneg (sub_nonneg.mpr ht.2),
        dist_eq_norm, dist_eq_norm]
    _ ≤ (1 - t) * eps + t * eps := by
      gcongr <;> linarith [ht.1, ht.2]
    _ = eps := by ring


theorem exists_source_segment_point_dist_le
    {a b a' b' : ℂ} {eps : ℝ}
    (ha : dist a' a ≤ eps) (hb : dist b' b ≤ eps)
    {z : ℂ} (hz : z ∈ segment ℝ a' b') :
    ∃ w ∈ segment ℝ a b, dist z w ≤ eps := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  refine ⟨AffineMap.lineMap a b t, ?_, ?_⟩
  · rw [segment_eq_image_lineMap]
    exact ⟨t, ht, rfl⟩
  · exact dist_lineMap_le_of_endpoint_dist_le ht ha hb


theorem segment_disjoint_of_perturbation
    {a b c d a' b' c' d' : ℂ} {eps r : ℝ}
    (ha : dist a' a ≤ eps) (hb : dist b' b ≤ eps)
    (hc : dist c' c ≤ eps) (hd : dist d' d ≤ eps)
    (hsep : ∀ x ∈ segment ℝ a b, ∀ y ∈ segment ℝ c d,
      r < dist x y)
    (heps : 2 * eps < r) :
    Disjoint (segment ℝ a' b') (segment ℝ c' d') := by
  rw [Set.disjoint_left]
  intro z hzab hzcd
  obtain ⟨x, hx, hzx⟩ :=
    exists_source_segment_point_dist_le ha hb hzab
  obtain ⟨y, hy, hzy⟩ :=
    exists_source_segment_point_dist_le hc hd hzcd
  have hxy := hsep x hx y hy
  have htri : dist x y ≤ dist x z + dist z y := dist_triangle x z y
  rw [dist_comm x z] at htri
  linarith


end StatMech.FrontierA
