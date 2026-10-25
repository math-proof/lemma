/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityMomentum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierKernelClosedForm
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheRapidityMomentum


namespace StatMech.FrontierD

noncomputable section

theorem intervalIntegral_zero_pi_sixVertexXiFourierTerm
    (lam : Real) (n : Nat) :
    (∫ alpha in (0 : Real)..Real.pi,
      sixVertexXiFourierTerm lam n alpha) = 0 := by
  let m : Real := n + 1
  have hm : m ≠ 0 := by
    dsimp [m]
    positivity
  have hscaled := intervalIntegral.mul_integral_comp_mul_left
    (a := (0 : Real)) (b := Real.pi) (f := Real.cos) m
  have hrhs : (∫ x in (0 : Real)..m * Real.pi, Real.cos x) = 0 := by
    rw [integral_cos]
    have hpos : Real.sin (m * Real.pi) = 0 := by
      dsimp [m]
      simpa only [Nat.cast_add, Nat.cast_one] using
        Real.sin_nat_mul_pi (n + 1)
    rw [hpos, Real.sin_zero, sub_zero]
  simp only [mul_zero] at hscaled
  rw [hrhs] at hscaled
  have hcoszero :
      (∫ alpha in (0 : Real)..Real.pi, Real.cos (m * alpha)) = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left hm
  unfold sixVertexXiFourierTerm
  change (∫ alpha in (0 : Real)..Real.pi,
    (2 * Real.exp (-(m * lam))) * Real.cos (m * alpha)) = 0
  rw [intervalIntegral.integral_const_mul, hcoszero, mul_zero]

theorem intervalIntegral_zero_pi_sixVertexXiFourier
    {lam : Real} (hlam : 0 < lam) :
    (∫ alpha in (0 : Real)..Real.pi,
      sixVertexXiFourier lam alpha) = Real.pi := by
  let K : TopologicalSpace.Compacts Real :=
    ⟨Set.uIcc (0 : Real) Real.pi, isCompact_uIcc⟩
  have hnorm : Summable (fun n : Nat =>
      ‖(sixVertexXiFourierTermContinuous lam n).restrict K‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) (summable_sixVertexFourierRootDensityMajorant hlam)
    rw [ContinuousMap.norm_le _
      (by
        unfold sixVertexFourierRootDensityMajorant
        positivity : 0 <= sixVertexFourierRootDensityMajorant lam n)]
    intro alpha
    exact norm_sixVertexXiFourierTerm_le lam n alpha
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hnorm
  have hswap' :
      (∑' n : Nat, ∫ alpha in (0 : Real)..Real.pi,
        sixVertexXiFourierTerm lam n alpha) =
      ∫ alpha in (0 : Real)..Real.pi,
        ∑' n : Nat, sixVertexXiFourierTerm lam n alpha := by
    simpa only [sixVertexXiFourierTermContinuous] using hswap
  have hseries :
      (∫ alpha in (0 : Real)..Real.pi,
        ∑' n : Nat, sixVertexXiFourierTerm lam n alpha) = 0 := by
    rw [<- hswap']
    rw [show (fun n : Nat => ∫ alpha in (0 : Real)..Real.pi,
        sixVertexXiFourierTerm lam n alpha) =
      (fun _ : Nat => 0) by
        funext n
        exact intervalIntegral_zero_pi_sixVertexXiFourierTerm lam n,
      tsum_zero]
  have hseriesInt : IntervalIntegrable
      (fun alpha => ∑' n : Nat, sixVertexXiFourierTerm lam n alpha)
      MeasureTheory.volume 0 Real.pi := by
    have hcont : Continuous
        (fun alpha => ∑' n : Nat, sixVertexXiFourierTerm lam n alpha) := by
      apply continuous_tsum
      · intro n
        unfold sixVertexXiFourierTerm
        fun_prop
      · exact summable_sixVertexFourierRootDensityMajorant hlam
      · intro n alpha
        exact norm_sixVertexXiFourierTerm_le lam n alpha
    exact hcont.intervalIntegrable _ _
  simp_rw [sixVertexXiFourier]
  rw [intervalIntegral.integral_add intervalIntegrable_const hseriesInt,
    intervalIntegral.integral_const, hseries]
  simp


end
end StatMech.FrontierD
