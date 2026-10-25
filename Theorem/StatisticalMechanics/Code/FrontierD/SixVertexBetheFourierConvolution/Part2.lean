/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution.Part2


namespace StatMech.FrontierD

noncomputable section

theorem intervalIntegral_shiftedCos_mul_sixVertexFourierRootDensity
    {lam : Real} (hlam : 0 < lam) (n : Nat) (alpha : Real) :
    (∫ beta in -Real.pi..Real.pi,
      Real.cos ((n + 1 : Real) * (alpha - beta)) *
        sixVertexFourierRootDensity lam beta) =
      Real.pi * Real.cos ((n + 1 : Real) * alpha) /
        Real.cosh ((n + 1 : Real) * lam) := by
  let K : TopologicalSpace.Compacts Real :=
    ⟨Set.uIcc (-Real.pi) Real.pi, isCompact_uIcc⟩
  have hnorm : Summable (fun j : Nat =>
      ‖(shiftedCosMulFourierRootDensityTermContinuous lam n j alpha).restrict K‖) := by
    apply Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => ?_) (summable_sixVertexFourierRootDensityMajorant hlam)
    rw [ContinuousMap.norm_le _
      (by
        unfold sixVertexFourierRootDensityMajorant
        positivity : 0 <= sixVertexFourierRootDensityMajorant lam j)]
    intro beta
    change |Real.cos ((n + 1 : Real) * (alpha - (beta : Real))) *
      sixVertexFourierRootDensityTerm lam j beta| <=
        sixVertexFourierRootDensityMajorant lam j
    rw [abs_mul]
    calc
      |Real.cos ((n + 1 : Real) * (alpha - beta))| *
          |sixVertexFourierRootDensityTerm lam j beta|
        <= 1 * sixVertexFourierRootDensityMajorant lam j := by
          apply mul_le_mul
          · exact abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
          · simpa only [Real.norm_eq_abs] using
              norm_sixVertexFourierRootDensityTerm_le hlam j (beta : Real)
          · exact abs_nonneg _
          · norm_num
      _ = sixVertexFourierRootDensityMajorant lam j := one_mul _
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hnorm
  have hswap' :
      (∑' j : Nat, ∫ beta in -Real.pi..Real.pi,
        Real.cos ((n + 1 : Real) * (alpha - beta)) *
          sixVertexFourierRootDensityTerm lam j beta) =
      ∫ beta in -Real.pi..Real.pi,
        (∑' j : Nat, Real.cos ((n + 1 : Real) * (alpha - beta)) *
          sixVertexFourierRootDensityTerm lam j beta) := by
    simpa only [shiftedCosMulFourierRootDensityTermContinuous] using hswap
  have hseries :
      (∫ beta in -Real.pi..Real.pi,
        Real.cos ((n + 1 : Real) * (alpha - beta)) *
          (∑' j : Nat, sixVertexFourierRootDensityTerm lam j beta)) =
      ∑' j : Nat, ∫ beta in -Real.pi..Real.pi,
        Real.cos ((n + 1 : Real) * (alpha - beta)) *
          sixVertexFourierRootDensityTerm lam j beta := by
    calc
      _ = ∫ beta in -Real.pi..Real.pi,
          (∑' j : Nat, Real.cos ((n + 1 : Real) * (alpha - beta)) *
            sixVertexFourierRootDensityTerm lam j beta) := by
        apply intervalIntegral.integral_congr
        intro beta _
        exact tsum_mul_left.symm
      _ = _ := hswap'.symm
  have hconstInt : IntervalIntegrable
      (fun beta => (1 / 2 : Real) *
        Real.cos ((n + 1 : Real) * (alpha - beta))) MeasureTheory.volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hseriesInt : IntervalIntegrable
      (fun beta => Real.cos ((n + 1 : Real) * (alpha - beta)) *
        (∑' j : Nat, sixVertexFourierRootDensityTerm lam j beta))
      MeasureTheory.volume (-Real.pi) Real.pi := by
    have hcont : Continuous
        (fun beta => ∑' j : Nat,
          sixVertexFourierRootDensityTerm lam j beta) := by
      apply continuous_tsum
      · intro j
        unfold sixVertexFourierRootDensityTerm
        fun_prop
      · exact summable_sixVertexFourierRootDensityMajorant hlam
      · intro j beta
        exact norm_sixVertexFourierRootDensityTerm_le hlam j beta
    exact ((by fun_prop : Continuous (fun beta =>
      Real.cos ((n + 1 : Real) * (alpha - beta)))).mul hcont).intervalIntegrable _ _
  simp_rw [sixVertexFourierRootDensity]
  rw [show (fun beta => Real.cos ((n + 1 : Real) * (alpha - beta)) *
      (1 / 2 + ∑' j : Nat, sixVertexFourierRootDensityTerm lam j beta)) =
      (fun beta => (1 / 2 : Real) *
          Real.cos ((n + 1 : Real) * (alpha - beta)) +
        Real.cos ((n + 1 : Real) * (alpha - beta)) *
          (∑' j : Nat, sixVertexFourierRootDensityTerm lam j beta)) by
      funext beta
      ring]
  rw [intervalIntegral.integral_add hconstInt hseriesInt,
    intervalIntegral.integral_const_mul,
    intervalIntegral_cos_succ_mul_sub, mul_zero, hseries]
  rw [show (fun j : Nat => ∫ beta in -Real.pi..Real.pi,
      Real.cos ((n + 1 : Real) * (alpha - beta)) *
        sixVertexFourierRootDensityTerm lam j beta) =
      (fun j : Nat => if n = j then
        Real.pi * Real.cos ((n + 1 : Real) * alpha) /
          Real.cosh ((n + 1 : Real) * lam) else 0) by
      funext j
      exact intervalIntegral_shiftedCos_mul_fourierRootDensityTerm
        lam n j alpha]
  rw [zero_add]
  simpa only [eq_comm] using
    (tsum_ite_eq n (fun _ : Nat =>
      Real.pi * Real.cos ((n + 1 : Real) * alpha) /
        Real.cosh ((n + 1 : Real) * lam)))


end
end StatMech.FrontierD
