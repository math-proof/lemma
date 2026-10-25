/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGenericShear.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAxisStaircase.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGenericShear


namespace StatMech.FrontierA

def kwShearXLinearEquiv (t : ℝ) : ℂ ≃ₗ[ℝ] ℂ where
  toFun := kwShearX t
  invFun := kwShearX (-t)
  left_inv z := by
    apply Complex.ext
    · simp [kwShearX]
    · simp [kwShearX]
  right_inv z := by
    apply Complex.ext
    · simp [kwShearX]
    · simp [kwShearX]
  map_add' z w := by
    apply Complex.ext
    · simp [kwShearX]; ring
    · simp [kwShearX]
  map_smul' r z := by
    apply Complex.ext
    · simp [kwShearX]; ring
    · simp [kwShearX]

def kwShearYLinearEquiv (t : ℝ) : ℂ ≃ₗ[ℝ] ℂ where
  toFun := kwShearY t
  invFun := kwShearY (-t)
  left_inv z := by
    apply Complex.ext
    · simp [kwShearY]
    · simp [kwShearY]
  right_inv z := by
    apply Complex.ext
    · simp [kwShearY]
    · simp [kwShearY]
  map_add' z w := by
    apply Complex.ext
    · simp [kwShearY]
    · simp [kwShearY]; ring
  map_smul' r z := by
    apply Complex.ext
    · simp [kwShearY]
    · simp [kwShearY]; ring


noncomputable def KWFiniteSimplePolygon.mapLinearEquiv
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (e : ℂ ≃ₗ[ℝ] ℂ) : KWFiniteSimplePolygon n where
  vertex := fun i ↦ e (polygon.vertex i)
  three_le := polygon.three_le
  vertex_injective := e.injective.comp polygon.vertex_injective
  vertex_not_strictly_between := by
    intro i j hji hjs hs
    apply polygon.vertex_not_strictly_between i j hji hjs
    exact e.toAffineEquiv.sbtw_map_iff.mp hs
  edgeInteriors_disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hzi' : Sbtw ℝ (polygon.vertex i) (e.symm z)
        (polygon.vertex (i + 1)) := by
      apply e.toAffineEquiv.sbtw_map_iff.mp
      simpa using hzi
    have hzj' : Sbtw ℝ (polygon.vertex j) (e.symm z)
        (polygon.vertex (j + 1)) := by
      apply e.toAffineEquiv.sbtw_map_iff.mp
      simpa using hzj
    exact Set.disjoint_left.mp (polygon.edgeInteriors_disjoint i j hij)
      hzi' hzj'

end StatMech.FrontierA
