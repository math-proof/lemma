/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part2
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

theorem squareLowerCapExpSum_le
    {r : Real} (hr0 : 0 <= r) (hr1 : r <= 1) (N : Nat) :
    squareLowerCapExpSum r N <=
      4 * finiteGeom r N ^ 3 * N := by
  have hgeom : 0 <= finiteGeom r N := by
    unfold finiteGeom
    positivity
  calc
    squareLowerCapExpSum r N <=
        (N : Real) ^ 2 * (4 * finiteGeom r N ^ 2 * r ^ N) := by
      unfold squareLowerCapExpSum
      calc
        (∑ xy : Fin N × Fin N, squareLayerExpSum r xy.1 xy.2 N) <=
            ∑ _xy : Fin N × Fin N,
              4 * finiteGeom r N ^ 2 * r ^ N := by
          apply Finset.sum_le_sum
          intro xy _
          exact sum_fin_prod_pow_l1_le_four_finiteGeom_sq
            r hr0 xy.1 xy.2 N
        _ = (N : Real) ^ 2 *
              (4 * finiteGeom r N ^ 2 * r ^ N) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
            nsmul_eq_mul, Nat.cast_mul]
          simp only [Fintype.card_fin]
          ring
    _ <= 4 * finiteGeom r N ^ 3 * N := by
      have hNr := nat_mul_pow_le_finiteGeom hr0 hr1 N
      calc
        (N : Real) ^ 2 * (4 * finiteGeom r N ^ 2 * r ^ N) =
            (4 * finiteGeom r N ^ 2 * N) * (N * r ^ N) := by ring
        _ <= (4 * finiteGeom r N ^ 2 * N) * finiteGeom r N := by
          gcongr
        _ = 4 * finiteGeom r N ^ 3 * N := by ring

theorem squareXSideExpSum_le
    {N : Nat} {r : Real} (hr0 : 0 <= r) (hr1 : r <= 1)
    (xBoundary : Fin N) :
    squareXSideExpSum r xBoundary <=
      4 * finiteGeom r N ^ 3 * N := by
  have hgeom : 0 <= finiteGeom r N := by
    unfold finiteGeom
    positivity
  have hdepth := sum_fin_pow_reverseDepth_le_finiteGeom
    (N := N) hr0 hr1
  unfold squareXSideExpSum
  rw [Fintype.sum_prod_type]
  calc
    (∑ y : Fin N, ∑ z : Fin N,
        squareLayerExpSum r xBoundary y (N - z.val)) <=
      ∑ y : Fin N, ∑ z : Fin N,
        4 * finiteGeom r N ^ 2 * r ^ (N - z.val) := by
      apply Finset.sum_le_sum
      intro y _
      apply Finset.sum_le_sum
      intro z _
      exact sum_fin_prod_pow_l1_le_four_finiteGeom_sq
        r hr0 xBoundary y (N - z.val)
    _ = (N : Real) *
        (4 * finiteGeom r N ^ 2 *
          (∑ z : Fin N, r ^ (N - z.val))) := by
      simp_rw [← Finset.mul_sum]
      simp [Fintype.card_fin]
      ring
    _ <= 4 * finiteGeom r N ^ 3 * N := by
      calc
        (N : Real) * (4 * finiteGeom r N ^ 2 *
            (∑ z : Fin N, r ^ (N - z.val))) <=
            N * (4 * finiteGeom r N ^ 2 * finiteGeom r N) := by
          gcongr
        _ = 4 * finiteGeom r N ^ 3 * N := by ring

theorem squareYSideExpSum_le
    {N : Nat} {r : Real} (hr0 : 0 <= r) (hr1 : r <= 1)
    (yBoundary : Fin N) :
    squareYSideExpSum r yBoundary <=
      4 * finiteGeom r N ^ 3 * N := by
  have hgeom : 0 <= finiteGeom r N := by
    unfold finiteGeom
    positivity
  have hdepth := sum_fin_pow_reverseDepth_le_finiteGeom
    (N := N) hr0 hr1
  unfold squareYSideExpSum
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : Fin N, ∑ z : Fin N,
        squareLayerExpSum r x yBoundary (N - z.val)) <=
      ∑ x : Fin N, ∑ z : Fin N,
        4 * finiteGeom r N ^ 2 * r ^ (N - z.val) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro z _
      exact sum_fin_prod_pow_l1_le_four_finiteGeom_sq
        r hr0 x yBoundary (N - z.val)
    _ = (N : Real) *
        (4 * finiteGeom r N ^ 2 *
          (∑ z : Fin N, r ^ (N - z.val))) := by
      simp_rw [← Finset.mul_sum]
      simp [Fintype.card_fin]
      ring
    _ <= 4 * finiteGeom r N ^ 3 * N := by
      calc
        (N : Real) * (4 * finiteGeom r N ^ 2 *
            (∑ z : Fin N, r ^ (N - z.val))) <=
            N * (4 * finiteGeom r N ^ 2 * finiteGeom r N) := by
          gcongr
        _ = 4 * finiteGeom r N ^ 3 * N := by ring


theorem squareCylinderCoordinateExpSum_le
    {N : Nat} {r : Real} (hr0 : 0 <= r) (hr1 : r <= 1)
    (west east south north : Fin N) :
    squareLowerCapExpSum r N +
        squareXSideExpSum r west + squareXSideExpSum r east +
        squareYSideExpSum r south + squareYSideExpSum r north <=
      20 * finiteGeom r N ^ 3 * N := by
  have hcap := squareLowerCapExpSum_le hr0 hr1 N
  have hwest := squareXSideExpSum_le hr0 hr1 west
  have heast := squareXSideExpSum_le hr0 hr1 east
  have hsouth := squareYSideExpSum_le hr0 hr1 south
  have hnorth := squareYSideExpSum_le hr0 hr1 north
  linarith


theorem squareCylinderCoordinateExpSum_le_inv
    {N : Nat} {r : Real} (hr0 : 0 <= r) (hr1 : r < 1)
    (west east south north : Fin N) :
    squareLowerCapExpSum r N +
        squareXSideExpSum r west + squareXSideExpSum r east +
        squareYSideExpSum r south + squareYSideExpSum r north <=
      20 * ((1 - r)⁻¹) ^ 3 * N := by
  have hgeom := finiteGeom_le_inv_one_sub hr0 hr1 N
  have hgeom0 : 0 <= finiteGeom r N := by
    unfold finiteGeom
    positivity
  have hinv0 : 0 <= (1 - r)⁻¹ := by
    positivity
  calc
    _ <= 20 * finiteGeom r N ^ 3 * N :=
      squareCylinderCoordinateExpSum_le hr0 hr1.le
        west east south north
    _ <= 20 * ((1 - r)⁻¹) ^ 3 * N := by
      gcongr


end
end StatMech.FrontierA
