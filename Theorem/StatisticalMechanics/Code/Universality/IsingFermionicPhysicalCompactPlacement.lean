/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly.Part2


namespace StatMech.Universality

open Filter Metric Set

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem abs_le_abs_of_mem_uIcc_zero
    {t h : Real} (ht : t ∈ Set.uIcc 0 h) : |t| ≤ |h| := by
  rcases Set.mem_uIcc.mp ht with ht | ht
  · rw [abs_of_nonneg ht.1, abs_of_nonneg (ht.1.trans ht.2)]
    exact ht.2
  · rw [abs_of_nonpos ht.2, abs_of_nonpos (ht.1.trans ht.2)]
    linarith

theorem diagonal_displacement_le_two_abs
    (z : Complex) (t : Real) (sgn : Bool) :
    dist
        (z + (t : Complex) *
          (if sgn then 1 + Complex.I else 1 - Complex.I)) z ≤
      2 * |t| := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real]
  have hdiag :
      ‖(if sgn then (1 + Complex.I : Complex) else 1 - Complex.I)‖ ≤ 2 := by
    cases sgn
    · calc
        ‖(1 - Complex.I : Complex)‖ ≤ ‖(1 : Complex)‖ + ‖Complex.I‖ :=
          norm_sub_le _ _
        _ = 2 := by norm_num
    · calc
        ‖(1 + Complex.I : Complex)‖ ≤ ‖(1 : Complex)‖ + ‖Complex.I‖ :=
          norm_add_le _ _
        _ = 2 := by norm_num
  rw [Real.norm_eq_abs]
  calc
    |t| * ‖(if sgn then (1 + Complex.I : Complex) else 1 - Complex.I)‖ ≤
        |t| * 2 := mul_le_mul_of_nonneg_left hdiag (abs_nonneg t)
    _ = 2 * |t| := by ring


theorem diagonalSegment_mapsTo_cthickening
    (K : Set Complex) (epsilon : Real) (z : Complex) (hz : z ∈ K) (h : Real)
    (hmesh : 2 * |h| ≤ epsilon) (sgn : Bool) :
    Set.MapsTo
      (fun t : Real => z + (t : Complex) *
        (if sgn then 1 + Complex.I else 1 - Complex.I))
      (Set.uIcc 0 h) (Metric.cthickening epsilon K) := by
  intro t ht
  apply Metric.mem_cthickening_of_dist_le _ z epsilon K hz
  exact (diagonal_displacement_le_two_abs z t sgn).trans
    ((mul_le_mul_of_nonneg_left
      (abs_le_abs_of_mem_uIcc_zero ht) (by norm_num)).trans hmesh)


theorem diagonalSegment_mapsTo_of_cthickening
    (U K : Set Complex) (epsilon : Real)
    (hKU : Metric.cthickening epsilon K ⊆ U)
    (z : Complex) (hz : z ∈ K) (h : Real)
    (hmesh : 2 * |h| ≤ epsilon) (sgn : Bool) :
    Set.MapsTo
      (fun t : Real => z + (t : Complex) *
        (if sgn then 1 + Complex.I else 1 - Complex.I))
      (Set.uIcc 0 h) U :=
  (diagonalSegment_mapsTo_cthickening K epsilon z hz h hmesh sgn).mono_right hKU


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
