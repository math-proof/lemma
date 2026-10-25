/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalPhaseReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonPerturbation.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleHomotopy.Part3


namespace StatMech.FrontierA

open scoped BigOperators

open Set

theorem dist_vertexLine_lt_certificate
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    (h : KWPolygonPerturbationCertificate polygon)
    {target : Fin n → ℂ} (htarget : dist target polygon.vertex < h.radius)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (AffineMap.lineMap polygon.vertex target t) polygon.vertex <
      h.radius := by
  rw [dist_lineMap_left]
  have hnorm : ‖t‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2
  calc
    ‖t‖ * dist polygon.vertex target ≤
        1 * dist polygon.vertex target :=
      mul_le_mul_of_nonneg_right hnorm dist_nonneg
    _ = dist target polygon.vertex := by rw [one_mul, dist_comm]
    _ < h.radius := htarget


end StatMech.FrontierA
