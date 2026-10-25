/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogTaylor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalCandidateBoundaryLimit
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogTaylor.Part4


namespace StatMech.FrontierD

noncomputable section

theorem lipschitzWith_mul_div_sixVertexFiniteRootDensity
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N) (hn : n <= N)
    (p : Fin n -> Real) {lower U G : Real} (hlower : 0 < lower)
    (hU : 0 <= U) (hG : 0 <= G)
    (hdensity : forall y, lower <= sixVertexFiniteRootDensity c N n p y)
    {u tau : Real -> Real} {Lu D : NNReal}
    (huLip : LipschitzWith Lu u) (huBound : forall y, |u y| <= U)
    (htauLip : LipschitzWith D tau) (htauBound : forall y, |tau y| <= G) :
    LipschitzWith
      (sixVertexLogOffsetQuotientLipschitzNNReal c lower U G Lu D)
      (fun y => u y * tau y /
        sixVertexFiniteRootDensity c N n p y) := by
  let rho := sixVertexFiniteRootDensity c N n p
  let LR : Real := sixVertexFiniteRootDensityLipschitzConstant c
  let C := sixVertexLogOffsetQuotientLipschitzBound c lower U G Lu D
  have hLR : 0 <= LR := by dsimp [LR]; exact NNReal.coe_nonneg _
  have hC : 0 <= C := by
    dsimp [C, sixVertexLogOffsetQuotientLipschitzBound]
    positivity
  have hcoe :
      (sixVertexLogOffsetQuotientLipschitzNNReal c lower U G Lu D : Real) =
        C := Real.coe_toNNReal _ hC
  have hrhoLip := lipschitzWith_sixVertexFiniteRootDensity hc hN hn p
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [Real.dist_eq, Real.dist_eq, hcoe]
  let dyz := |y - z|
  have hudiff : |u y - u z| <= (Lu : Real) * dyz := by
    simpa [Real.dist_eq, dyz] using huLip.dist_le_mul y z
  have htaudiff : |tau y - tau z| <= (D : Real) * dyz := by
    simpa [Real.dist_eq, dyz] using htauLip.dist_le_mul y z
  have hrhodiff : |rho z - rho y| <= LR * dyz := by
    have h := hrhoLip.dist_le_mul z y
    simpa only [Real.dist_eq, rho, LR, dyz, abs_sub_comm] using h
  have hry : 0 < rho y := hlower.trans_le (hdensity y)
  have hrz : 0 < rho z := hlower.trans_le (hdensity z)
  have hrearrange :
      u y * tau y / rho y - u z * tau z / rho z =
        (u y - u z) * tau y / rho y +
        u z * (tau y - tau z) / rho y +
        u z * tau z * (rho z - rho y) / (rho y * rho z) := by
    field_simp [hry.ne', hrz.ne']
    ring
  rw [hrearrange]
  calc
    |_ + _ + _| <= |_| + |_| + |_| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ <= ((Lu : Real) * dyz * G) / lower +
        (U * ((D : Real) * dyz)) / lower +
        (U * G * (LR * dyz)) / lower ^ 2 := by
      rw [abs_div, abs_div, abs_div, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_mul, abs_of_pos hry, abs_of_pos hrz]
      apply add_le_add
      · apply add_le_add
        · have hnum := mul_le_mul hudiff (htauBound y)
            (abs_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (abs_nonneg _))
          exact (div_le_div_of_nonneg_right hnum hry.le).trans
            (div_le_div_of_nonneg_left
              (mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) (abs_nonneg _)) hG)
              hlower (hdensity y))
        · have hnum := mul_le_mul (huBound z) htaudiff
            (abs_nonneg _) hU
          exact (div_le_div_of_nonneg_right hnum hry.le).trans
            (div_le_div_of_nonneg_left
              (mul_nonneg hU (mul_nonneg (NNReal.coe_nonneg _) (abs_nonneg _)))
              hlower (hdensity y))
      · have hprod : |u z| * |tau z| <= U * G :=
          mul_le_mul (huBound z) (htauBound z) (abs_nonneg _) hU
        have hnum : |u z| * |tau z| * |rho z - rho y| <=
            U * G * (LR * dyz) :=
          mul_le_mul hprod hrhodiff (abs_nonneg _) (mul_nonneg hU hG)
        have hdenLower : lower ^ 2 <= rho y * rho z := by
          nlinarith [hdensity y, hdensity z]
        exact (div_le_div_of_nonneg_right hnum
            (mul_nonneg hry.le hrz.le)).trans
          (div_le_div_of_nonneg_left
            (mul_nonneg (mul_nonneg hU hG)
              (mul_nonneg hLR (abs_nonneg (y - z))))
            (sq_pos_of_pos hlower) hdenLower)
    _ = C * |y - z| := by
      dsimp [C, sixVertexLogOffsetQuotientLipschitzBound, dyz, LR]
      ring

theorem abs_sixVertexRegularizedBetheLogKernel_sub_linearization_le
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (a b : Real) :
    |sixVertexRegularizedBetheLogKernel c epsilon b -
        sixVertexRegularizedBetheLogKernel c epsilon a -
      sixVertexRegularizedBetheLogNormDerivative c epsilon a * (b - a)| <=
        (sixVertexRegularizedBetheLogNormSecondDerivativeNNReal
          c epsilon : Real) * |b - a| ^ 2 := by
  exact abs_sub_sub_deriv_mul_le_of_lipschitz
    (fun x => hasDerivAt_sixVertexRegularizedBetheLogKernel hc hepsilon)
    (lipschitzWith_sixVertexRegularizedBetheLogNormDerivative hc hepsilon) a b

end
end StatMech.FrontierD
