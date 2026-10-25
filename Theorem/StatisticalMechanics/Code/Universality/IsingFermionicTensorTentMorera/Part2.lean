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
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

theorem VanishingRectangleContourError.contour_tendsto_zero
    {F : Nat -> Complex -> Complex}
    (H : VanishingRectangleContourError F) (z w : Complex) :
    Tendsto (fun n => Complex.wedgeIntegral z w (F n) +
      Complex.wedgeIntegral w z (F n)) atTop (nhds 0) := by
  apply squeeze_zero_norm (fun n => H.contour_norm_le z w n)
  exact H.error_tendsto_zero z w


theorem VanishingRectangleContourError.contour_tendsto_zero_comp
    {F : Nat -> Complex -> Complex}
    (H : VanishingRectangleContourError F) {sigma : Nat -> Nat}
    (hsigma : Tendsto sigma atTop atTop) (z w : Complex) :
    Tendsto (fun n => Complex.wedgeIntegral z w (F (sigma n)) +
      Complex.wedgeIntegral w z (F (sigma n))) atTop (nhds 0) :=
  (H.contour_tendsto_zero z w).comp hsigma


theorem norm_wedgeContour_le_of_uniformNorm
    (F : Complex -> Complex) (epsilon : Real)
    (hF : forall z, norm (F z) <= epsilon) (z w : Complex) :
    norm (Complex.wedgeIntegral z w F + Complex.wedgeIntegral w z F) <=
      2 * epsilon * (|w.re - z.re| + |w.im - z.im|) := by
  let A : Complex := ∫ x : Real in z.re..w.re, F (x + z.im * Complex.I)
  let B : Complex := ∫ x : Real in z.re..w.re, F (x + w.im * Complex.I)
  let C : Complex := ∫ y : Real in z.im..w.im, F (w.re + y * Complex.I)
  let D : Complex := ∫ y : Real in z.im..w.im, F (z.re + y * Complex.I)
  have hA : norm A <= epsilon * |w.re - z.re| := by
    dsimp only [A]
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x _hx => hF (x + z.im * Complex.I))
  have hB : norm B <= epsilon * |w.re - z.re| := by
    dsimp only [B]
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x _hx => hF (x + w.im * Complex.I))
  have hC : norm C <= epsilon * |w.im - z.im| := by
    dsimp only [C]
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun y _hy => hF (w.re + y * Complex.I))
  have hD : norm D <= epsilon * |w.im - z.im| := by
    dsimp only [D]
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun y _hy => hF (z.re + y * Complex.I))
  rw [Complex.wedgeIntegral_add_wedgeIntegral_eq]
  change norm (A - B + Complex.I * C - Complex.I * D) <= _
  calc
    norm (A - B + Complex.I * C - Complex.I * D) <=
        norm (A - B + Complex.I * C) + norm (Complex.I * D) :=
      norm_sub_le _ _
    _ <= (norm (A - B) + norm (Complex.I * C)) + norm (Complex.I * D) :=
      by gcongr; exact norm_add_le _ _
    _ <= ((norm A + norm B) + norm (Complex.I * C)) + norm (Complex.I * D) :=
      by gcongr; exact norm_sub_le _ _
    _ <= 2 * epsilon * (|w.re - z.re| + |w.im - z.im|) := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
      nlinarith


end
end StatMech.Universality
