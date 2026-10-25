/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderEndpointLift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTwoPointComparison.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderEndpointLift.Part3
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

theorem fkRectHorizontalCylinder_fixedEndpoint_add_correction
    (R : FKRectTorus) :
    fkRectHorizontalCylinderFixedEndpointDisplacement R.height +
        fkRectHorizontalCylinderFixedEndpointCorrection =
      fkRectHorizontalCylinderReflectedDiagonalDisplacement R.height := by
  funext i
  fin_cases i <;>
    simp [fkRectHorizontalCylinderFixedEndpointDisplacement,
      fkRectHorizontalCylinderSquareLiftedDisplacement,
      fkRectHorizontalCylinderFixedEndpointCorrection,
      fkRectHorizontalCylinderReflectedDiagonalDisplacement]


theorem fkQgt4CriticalFreeTwoPoint_reflectedDiagonal_eq_exact
    {q : Real} (hq : 4 < q) (height : Nat) :
    fkQgt4CriticalFreeTwoPoint hq
        (fkRectHorizontalCylinderReflectedDiagonalDisplacement height) =
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq (height / 2) := by
  let S := fkQgt4CoordinateSignBoxSym fun i : Fin 2 => i = 1
  have hsym := fkQgt4CriticalFreeTwoPoint_boxSym hq S
    (fkRectHorizontalCylinderReflectedDiagonalDisplacement height)
  have hmap : S.τ
      (fkRectHorizontalCylinderReflectedDiagonalDisplacement height) =
        fkQgt4ExactDiagonalSite (height / 2) := by
    funext i
    fin_cases i <;>
      simp [S, fkQgt4CoordinateSignBoxSym,
        fkRectHorizontalCylinderReflectedDiagonalDisplacement,
        fkQgt4ExactDiagonalSite]
  rw [hmap] at hsym
  simpa [fkQgt4CriticalFreeTwoPoint,
    fkQgt4CriticalFreeExactDiagonalTwoPoint] using hsym.symm


theorem fkQgt4CriticalFreeTwoPoint_fixedEndpoint_mul_correction_le_exact
    {q : Real} (hq : 4 < q) (R : FKRectTorus) :
    fkQgt4CriticalFreeTwoPoint hq
          (fkRectHorizontalCylinderFixedEndpointDisplacement R.height) *
        fkQgt4CriticalFreeTwoPoint hq
          fkRectHorizontalCylinderFixedEndpointCorrection <=
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height / 2) := by
  have hmul := fkQgt4CriticalFreeTwoPoint_add_supermultiplicative hq
    (fkRectHorizontalCylinderFixedEndpointDisplacement R.height)
    fkRectHorizontalCylinderFixedEndpointCorrection
  rw [fkRectHorizontalCylinder_fixedEndpoint_add_correction R] at hmul
  rwa [fkQgt4CriticalFreeTwoPoint_reflectedDiagonal_eq_exact hq R.height]
    at hmul


theorem fkQgt4CriticalFreeTwoPoint_fixedEndpoint_le_exact_div
    {q : Real} (hq : 4 < q) (R : FKRectTorus) :
    fkQgt4CriticalFreeTwoPoint hq
        (fkRectHorizontalCylinderFixedEndpointDisplacement R.height) <=
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height / 2) /
        fkQgt4CriticalFreeTwoPoint hq
          fkRectHorizontalCylinderFixedEndpointCorrection := by
  rw [le_div_iff₀ (fkQgt4CriticalFreeTwoPoint_pos hq
    fkRectHorizontalCylinderFixedEndpointCorrection)]
  exact fkQgt4CriticalFreeTwoPoint_fixedEndpoint_mul_correction_le_exact
    hq R


theorem fkQgt4CriticalFreeTwoPoint_sq_le_exactDiagonal_of_coordSub
    {q : Real} (hq : 4 < q) (x : Site 2) (n : Nat)
    (hcoord : x 0 - x 1 = (n : Int)) :
    fkQgt4CriticalFreeTwoPoint hq x ^ 2 <=
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq n := by
  let swap := FK.rot_permBoxSym 2 (Equiv.swap (0 : Fin 2) 1)
  let neg := fkQgt4CoordinateSignBoxSym fun _ : Fin 2 => true
  let y := neg.τ (swap.τ x)
  have hswap : fkQgt4CriticalFreeTwoPoint hq (swap.τ x) =
      fkQgt4CriticalFreeTwoPoint hq x :=
    fkQgt4CriticalFreeTwoPoint_boxSym hq swap x
  have hneg : fkQgt4CriticalFreeTwoPoint hq y =
      fkQgt4CriticalFreeTwoPoint hq (swap.τ x) := by
    exact fkQgt4CriticalFreeTwoPoint_boxSym hq neg (swap.τ x)
  have hy0 : y 0 = -(x 1) := by
    simp [y, neg, swap, fkQgt4CoordinateSignBoxSym,
      FK.rot_permBoxSym, FK.rot_permEquiv]
  have hy1 : y 1 = -(x 0) := by
    simp [y, neg, swap, fkQgt4CoordinateSignBoxSym,
      FK.rot_permBoxSym, FK.rot_permEquiv]
  have hadd : x + y =
      fkRectHorizontalCylinderReflectedDiagonalDisplacement (2 * n) := by
    funext i
    fin_cases i <;>
      simp [fkRectHorizontalCylinderReflectedDiagonalDisplacement,
        hy0, hy1] <;>
      omega
  have hmul := fkQgt4CriticalFreeTwoPoint_add_supermultiplicative hq x y
  rw [hneg, hswap, hadd,
    fkQgt4CriticalFreeTwoPoint_reflectedDiagonal_eq_exact hq (2 * n)] at hmul
  simpa [pow_two] using hmul


theorem fkQgt4CriticalFreeTwoPoint_squareLiftedDisplacement_le_sqrt_exact
    {q : Real} (hq : 4 < q) (R : FKRectTorus) (rawDx : Int) :
    fkQgt4CriticalFreeTwoPoint hq
        (fkRectHorizontalCylinderSquareLiftedDisplacement rawDx R.height) <=
      Real.sqrt
        (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1)) := by
  let x := fkRectHorizontalCylinderSquareLiftedDisplacement rawDx R.height
  have hheight : 1 <= R.height := by
    have hh := R.height_gt_two
    omega
  have hsq := fkQgt4CriticalFreeTwoPoint_sq_le_exactDiagonal_of_coordSub
    hq x (R.height - 1) (by
      dsimp [x]
      rw [fkRectHorizontalCylinderSquareLiftedDisplacement_coord_sub]
      rw [Nat.cast_sub hheight]
      norm_num)
  have hx : 0 <= fkQgt4CriticalFreeTwoPoint hq x :=
    (fkQgt4CriticalFreeTwoPoint_pos hq x).le
  have hdiag : 0 <=
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1) :=
    (fkQgt4CriticalFreeExactDiagonalTwoPoint_pos hq (R.height - 1)).le
  have hsqrt := Real.sqrt_nonneg
    (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1))
  change fkQgt4CriticalFreeTwoPoint hq x <= _
  nlinarith [Real.sq_sqrt hdiag]

end
end StatMech.FrontierD
