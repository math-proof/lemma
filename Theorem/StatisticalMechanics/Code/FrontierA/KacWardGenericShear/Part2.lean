/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGenericShear.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAxisStaircase.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardGenericShear.Part2


namespace StatMech.FrontierA

@[simp] theorem KWFiniteSimplePolygon.mapLinearEquiv_vertex
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (e : ℂ ≃ₗ[ℝ] ℂ) (i : Fin n) :
    (polygon.mapLinearEquiv e).vertex i = e (polygon.vertex i) := rfl

@[simp] theorem KWFiniteSimplePolygon.mapLinearEquiv_edgeVector
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (e : ℂ ≃ₗ[ℝ] ℂ) (i : Fin n) :
    (polygon.mapLinearEquiv e).edgeVector i = e (polygon.edgeVector i) := by
  simp only [KWFiniteSimplePolygon.edgeVector, mapLinearEquiv_vertex,
    map_sub]


theorem exists_real_not_mem_finset (s : Finset ℝ) :
    ∃ t : ℝ, t ∉ s := by
  have hinfinite : (Set.univ \ (↑s : Set ℝ)).Infinite :=
    Set.infinite_univ.diff s.finite_toSet
  obtain ⟨t, _, ht⟩ := hinfinite.nonempty
  exact ⟨t, ht⟩


theorem KWFiniteSimplePolygon.exists_shearX_re_ne_zero
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    ∃ t : ℝ, ∀ i : Fin n, (kwShearX t (polygon.edgeVector i)).re ≠ 0 := by
  classical
  let forbidden : Finset ℝ := Finset.univ.image fun i : Fin n ↦
    -(polygon.edgeVector i).re / (polygon.edgeVector i).im
  obtain ⟨t, ht⟩ := exists_real_not_mem_finset forbidden
  refine ⟨t, ?_⟩
  intro i hzero
  by_cases him : (polygon.edgeVector i).im = 0
  · have hre : (polygon.edgeVector i).re = 0 := by
      rw [kwShearX_re, him, mul_zero, add_zero] at hzero
      exact hzero
    have hedge : polygon.edgeVector i = 0 := by
      apply Complex.ext
      · exact hre
      · exact him
    unfold KWFiniteSimplePolygon.edgeVector at hedge
    exact polygon.vertex_injective.ne (polygon.add_one_ne_self i) (sub_eq_zero.mp hedge)
  · apply ht
    simp only [forbidden, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨i, ?_⟩
    simp only [kwShearX_re] at hzero
    symm
    apply (eq_div_iff him).mpr
    linarith


theorem KWFiniteSimplePolygon.exists_generic_shear
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    ∃ tx ty : ℝ, ∀ i : Fin n,
      (kwShearY ty (kwShearX tx (polygon.edgeVector i))).re ≠ 0 ∧
      (kwShearY ty (kwShearX tx (polygon.edgeVector i))).im ≠ 0 := by
  classical
  obtain ⟨tx, hx⟩ := polygon.exists_shearX_re_ne_zero
  let forbidden : Finset ℝ := Finset.univ.image fun i : Fin n ↦
    -(kwShearX tx (polygon.edgeVector i)).im /
      (kwShearX tx (polygon.edgeVector i)).re
  obtain ⟨ty, hty⟩ := exists_real_not_mem_finset forbidden
  refine ⟨tx, ty, ?_⟩
  intro i
  constructor
  · simpa using hx i
  · intro hzero
    apply hty
    simp only [forbidden, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨i, ?_⟩
    simp only [kwShearY_im] at hzero
    symm
    apply (eq_div_iff (hx i)).mpr
    linarith


theorem KWFiniteSimplePolygon.exists_generic_coordinate_polygon
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    ∃ tx ty : ℝ,
      let e := (kwShearXLinearEquiv tx).trans (kwShearYLinearEquiv ty)
      ∀ i : Fin n,
        ((polygon.mapLinearEquiv e).edgeVector i).re ≠ 0 ∧
        ((polygon.mapLinearEquiv e).edgeVector i).im ≠ 0 := by
  obtain ⟨tx, ty, hgeneric⟩ := polygon.exists_generic_shear
  refine ⟨tx, ty, ?_⟩
  dsimp only
  intro i
  rw [polygon.mapLinearEquiv_edgeVector]
  simpa only [LinearEquiv.trans_apply, kwShearXLinearEquiv,
    kwShearYLinearEquiv] using hgeneric i

end StatMech.FrontierA
