/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeNonperiodicQuadrature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetTestQuadrature
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeNonperiodicQuadrature
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos_of_lipschitz_nonperiodic
    {c : Real} (hc : 2 < c) {N m r : Nat} (hN : 0 < N) (hm : 0 < m)
    (hcharge : N = 2 * m + 2 * r) {p : Fin m -> Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N m p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall y, lower <= sixVertexFiniteRootDensity c N m p y)
    (x : Real) {tau : Real -> Real} {D : NNReal} {G : Real}
    (htauLip : LipschitzWith D tau)
    (htauBound : forall y, |tau y| <= G) :
    |(∑ j, sixVertexContinuousOffsetKernel c x (p j) * tau (p j) /
          sixVertexFiniteRootDensity c N m p (p j)) / N -
        ∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c x y * tau y| <=
      sixVertexFixedChargeNonperiodicOffsetTestError c N r lower G D := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  let rho := sixVertexFiniteRootDensity c N (n + 1) p
  let f : Real -> Real := fun y =>
    sixVertexContinuousOffsetKernel c x y * tau y / rho y
  let F := (sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)) * G / lower
  have hrho : Continuous rho :=
    continuous_sixVertexFiniteRootDensity hc N (n + 1) p
  have hkernel : Continuous (sixVertexContinuousOffsetKernel c x) := by
    unfold sixVertexContinuousOffsetKernel
    exact (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous.div
      (by
        unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
          sixVertexRootDensityScale
        fun_prop)
      (fun y => (sixVertexRootDensityWeight_pos hc y).ne')
  have hf : Continuous f :=
    (hkernel.mul htauLip.continuous).div hrho
      (fun y => (hlower.trans_le (hdensity y)).ne')
  have hfLip : LipschitzWith
      (sixVertexOffsetQuotientLipschitzNNReal c lower G D) f := by
    exact lipschitzWith_sixVertexContinuousOffsetKernel_mul_div_finiteDensity
      hc hN (by omega) p hlower hdensity htauLip htauBound x
  have hfBound : forall y, |f y| <= F := by
    intro y
    have hkernelBound := abs_sixVertexRootDensityKernel_div_weight_le hc x y
    have hrhoLower := hdensity y
    have hrhoPos : 0 < rho y := hlower.trans_le hrhoLower
    have hG : 0 <= G := (abs_nonneg (tau 0)).trans (htauBound 0)
    have hratio : 0 <= sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1) := by
      have hd := one_lt_sixVertexAnisotropyMagnitude hc
      positivity
    dsimp [f, F]
    rw [abs_div, abs_mul, abs_of_pos hrhoPos]
    have hprod := mul_le_mul hkernelBound (htauBound y)
      (abs_nonneg _) hratio
    calc
      |sixVertexContinuousOffsetKernel c x y| * |tau y| / rho y <=
          ((sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1)) * G) / rho y :=
        div_le_div_of_nonneg_right hprod hrhoPos.le
      _ <= ((sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1)) * G) / lower :=
        div_le_div_of_nonneg_left (mul_nonneg hratio hG) hlower hrhoLower
  have hquad :=
    abs_empiricalLipschitz_sub_finiteDensityIntegral_fixedCharge_nonperiodic
      hc hN hcharge hopen hsol hlower hdensity hf hfLip hfBound
  change |(∑ j, f (p j)) / N -
      ∫ y in -Real.pi..Real.pi, f y * rho y| <= _ at hquad
  have hintegral :
      (∫ y in -Real.pi..Real.pi, f y * rho y) =
        ∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c x y * tau y := by
    apply intervalIntegral.integral_congr
    intro y _
    dsimp [f, rho]
    field_simp [(hlower.trans_le (hdensity y)).ne']
  rw [hintegral] at hquad
  simpa [f, F, sixVertexFixedChargeNonperiodicOffsetTestError,
    sixVertexFixedChargeOffsetTestError] using hquad

theorem tendsto_sixVertexFixedChargeNonperiodicOffsetTestError
    (c : Real) (r : Nat) {lower : Real} (hlower : 0 < lower)
    (G : Real) (D : NNReal) :
    Filter.Tendsto (fun k => sixVertexFixedChargeNonperiodicOffsetTestError c
      (sixVertexFourWidth r k) r lower G D) Filter.atTop (nhds 0) := by
  let F := (sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)) * G / lower
  let E := 2 * F +
    sixVertexFiniteRootDensityUniformBound c * F *
      ((2 * (r : Real) + 1) / lower)
  have hwidthNat : Filter.Tendsto (sixVertexFourWidth r)
      Filter.atTop Filter.atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Filter.Tendsto
      (fun k : Nat => (sixVertexFourWidth r k : Real))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthNat
  have hbase := tendsto_sixVertexFixedChargeOffsetTestError
    c r hlower G D
  have hextra : Filter.Tendsto
      (fun k : Nat => E / (sixVertexFourWidth r k : Real))
      Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop hwidth
  have hadd := hbase.add hextra
  have hfun :
      (fun k => sixVertexFixedChargeNonperiodicOffsetTestError c
        (sixVertexFourWidth r k) r lower G D) =
      (fun k => sixVertexFixedChargeOffsetTestError c
          (sixVertexFourWidth r k) r lower G D +
        E / (sixVertexFourWidth r k : Real)) := by
    funext k
    dsimp [E, F]
    unfold sixVertexFixedChargeNonperiodicOffsetTestError
    field_simp [hlower.ne']
    ring
  rw [hfun]
  simpa only [add_zero] using hadd

end
end StatMech.FrontierD
