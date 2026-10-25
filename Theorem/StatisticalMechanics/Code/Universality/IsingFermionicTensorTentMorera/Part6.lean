/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Def.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part4


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

theorem reflectedRadialBilinearCellPathIntegral_eq_contour
    (mesh : Real) (a00 a10 a01 a11 : Complex) :
    reflectedRadialBilinearCellPathIntegral mesh a00 a10 a01 a11 =
      reflectedRadialBilinearCellContour mesh a00 a10 a01 a11 := by
  have hbottom : (∫ x : Real in 0..1,
      complexBilinearCell a00 a10 a01 a11 x 0) = (a00 + a10) / 2 := by
    simpa [complexBilinearCell] using
      intervalIntegral_complexAffine_unit a00 a10
  have hright : (∫ y : Real in 0..1,
      complexBilinearCell a00 a10 a01 a11 1 y) = (a10 + a11) / 2 := by
    simpa [complexBilinearCell] using
      intervalIntegral_complexAffine_unit a10 a11
  have htop : (∫ x : Real in 0..1,
      complexBilinearCell a00 a10 a01 a11 x 1) = (a01 + a11) / 2 := by
    simpa [complexBilinearCell] using
      intervalIntegral_complexAffine_unit a01 a11
  have hleft : (∫ y : Real in 0..1,
      complexBilinearCell a00 a10 a01 a11 0 y) = (a00 + a01) / 2 := by
    simpa [complexBilinearCell] using
      intervalIntegral_complexAffine_unit a00 a01
  unfold reflectedRadialBilinearCellPathIntegral
    reflectedRadialBilinearCellContour
  simp_rw [intervalIntegral.integral_mul_const]
  rw [hbottom, hright, htop, hleft]
  ring


theorem reflectedRadialBilinearCellContour_eq_zero_of_cellCR
    (mesh : Real) (a00 a10 a01 a11 : Complex)
    (hCR : a01 - a10 = Complex.I * (a11 - a00)) :
    reflectedRadialBilinearCellContour mesh a00 a10 a01 a11 = 0 := by
  rw [reflectedRadialBilinearCellContour_eq]
  have h : a10 - a01 = -Complex.I * (a11 - a00) := by
    linear_combination -hCR
  rw [h]
  ring

theorem reflectedRadialBilinearCellPathIntegral_eq_zero_of_cellCR
    (mesh : Real) (a00 a10 a01 a11 : Complex)
    (hCR : a01 - a10 = Complex.I * (a11 - a00)) :
    reflectedRadialBilinearCellPathIntegral mesh a00 a10 a01 a11 = 0 := by
  rw [reflectedRadialBilinearCellPathIntegral_eq_contour]
  exact reflectedRadialBilinearCellContour_eq_zero_of_cellCR
    mesh a00 a10 a01 a11 hCR


theorem IsingCellCRAt.div_const
    {F : Nat -> Nat -> Complex} {i j : Nat}
    (hCR : IsingCellCRAt F i j) (c : Complex) :
    IsingCellCRAt (fun a b => F a b / c) i j := by
  unfold IsingCellCRAt at hCR ⊢
  rw [← sub_div, ← sub_div, hCR]
  ring


end
end StatMech.Universality
