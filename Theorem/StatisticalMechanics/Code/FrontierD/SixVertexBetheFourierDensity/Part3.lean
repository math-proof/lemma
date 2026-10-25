/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierDensity.Part3
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem intervalIntegral_sixVertexFourierRootDensityTerm
    (lam : Real) (n : Nat) :
    ∫ alpha in -Real.pi..Real.pi,
      sixVertexFourierRootDensityTerm lam n alpha = 0 := by
  let m : Real := n + 1
  have hm : m ≠ 0 := by
    dsimp [m]
    positivity
  have hscaled := intervalIntegral.mul_integral_comp_mul_left
    (a := -Real.pi) (b := Real.pi) (f := Real.cos) m
  have hrhs :
      (∫ x in m * (-Real.pi)..m * Real.pi, Real.cos x) = 0 := by
    rw [integral_cos]
    have hpos : Real.sin (m * Real.pi) = 0 := by
      dsimp [m]
      simpa only [Nat.cast_add, Nat.cast_one] using
        Real.sin_nat_mul_pi (n + 1)
    have hneg : Real.sin (m * (-Real.pi)) = 0 := by
      rw [show m * (-Real.pi) = -(m * Real.pi) by ring, Real.sin_neg, hpos, neg_zero]
    rw [hpos, hneg, sub_zero]
  rw [hrhs] at hscaled
  have hcoszero :
      (∫ alpha in -Real.pi..Real.pi, Real.cos (m * alpha)) = 0 := by
    exact (mul_eq_zero.mp hscaled).resolve_left hm
  unfold sixVertexFourierRootDensityTerm
  change (∫ alpha in -Real.pi..Real.pi,
    Real.cos (m * alpha) / Real.cosh (m * lam)) = 0
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const, hcoszero,
    zero_mul]

theorem intervalIntegral_tsum_sixVertexFourierRootDensityTerm
    {lam : Real} (hlam : 0 < lam) :
    ∫ alpha in -Real.pi..Real.pi,
      (∑' n : Nat, sixVertexFourierRootDensityTerm lam n alpha) = 0 := by
  let K : TopologicalSpace.Compacts Real :=
    ⟨Set.uIcc (-Real.pi) Real.pi, isCompact_uIcc⟩
  have hnorm : Summable (fun n : Nat =>
      ‖(sixVertexFourierRootDensityTermContinuous lam n).restrict K‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) (summable_sixVertexFourierRootDensityMajorant hlam)
    rw [ContinuousMap.norm_le _
      (by
        unfold sixVertexFourierRootDensityMajorant
        positivity : 0 <= sixVertexFourierRootDensityMajorant lam n)]
    intro alpha
    exact norm_sixVertexFourierRootDensityTerm_le hlam n alpha
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hnorm
  rw [show (fun alpha => ∑' n : Nat,
      (sixVertexFourierRootDensityTermContinuous lam n) alpha) =
      (fun alpha => ∑' n : Nat,
        sixVertexFourierRootDensityTerm lam n alpha) by rfl] at hswap
  rw [<- hswap]
  rw [show (fun i : Nat => ∫ x in -Real.pi..Real.pi,
      (sixVertexFourierRootDensityTermContinuous lam i) x) =
      (fun _ : Nat => 0) by
        funext i
        change (∫ x in -Real.pi..Real.pi,
          sixVertexFourierRootDensityTerm lam i x) = 0
        exact intervalIntegral_sixVertexFourierRootDensityTerm lam i]
  exact tsum_zero


theorem intervalIntegral_sixVertexFourierRootDensity
    {lam : Real} (hlam : 0 < lam) :
    ∫ alpha in -Real.pi..Real.pi,
      sixVertexFourierRootDensity lam alpha = Real.pi := by
  have hseriesContinuous : Continuous
      (fun alpha => ∑' n : Nat,
        sixVertexFourierRootDensityTerm lam n alpha) := by
    apply continuous_tsum
    · intro n
      unfold sixVertexFourierRootDensityTerm
      fun_prop
    · exact summable_sixVertexFourierRootDensityMajorant hlam
    · intro n alpha
      exact norm_sixVertexFourierRootDensityTerm_le hlam n alpha
  have hseries : IntervalIntegrable
      (fun alpha => ∑' n : Nat,
        sixVertexFourierRootDensityTerm lam n alpha)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    hseriesContinuous.intervalIntegrable _ _
  simp_rw [sixVertexFourierRootDensity]
  rw [intervalIntegral.integral_add intervalIntegrable_const hseries,
    intervalIntegral_tsum_sixVertexFourierRootDensityTerm hlam,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

end
end StatMech.FrontierD
