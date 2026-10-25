/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution


namespace StatMech.FrontierD

noncomputable section

theorem norm_sixVertexXiFourierTerm_le
    (lam : Real) (n : Nat) (alpha : Real) :
    ‖sixVertexXiFourierTerm lam n alpha‖ <=
      sixVertexFourierRootDensityMajorant lam n := by
  rw [sixVertexXiFourierTerm, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 <= (2 : Real)),
    abs_of_pos (Real.exp_pos _)]
  have hcos : |Real.cos ((n + 1 : Real) * alpha)| <= 1 :=
    abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  calc
    2 * Real.exp (-((n + 1 : Real) * lam)) *
        |Real.cos ((n + 1 : Real) * alpha)|
      <= 2 * Real.exp (-((n + 1 : Real) * lam)) * 1 := by gcongr
    _ = sixVertexFourierRootDensityMajorant lam n := by
      rw [sixVertexFourierRootDensityMajorant, mul_one, <- Real.exp_nat_mul]
      congr 2
      push_cast
      ring

theorem summable_sixVertexXiFourierTerm
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Summable (fun n => sixVertexXiFourierTerm lam n alpha) :=
  (summable_sixVertexFourierRootDensityMajorant hlam).of_norm_bounded
    (fun n => norm_sixVertexXiFourierTerm_le lam n alpha)

theorem continuous_sixVertexXiFourier
    {lam : Real} (hlam : 0 < lam) :
    Continuous (sixVertexXiFourier lam) := by
  apply continuous_const.add
  apply continuous_tsum
  · intro n
    unfold sixVertexXiFourierTerm
    fun_prop
  · exact summable_sixVertexFourierRootDensityMajorant hlam
  · intro n alpha
    exact norm_sixVertexXiFourierTerm_le lam n alpha

theorem intervalIntegral_cos_succ_mul_sub (n : Nat) (alpha : Real) :
    (∫ beta in -Real.pi..Real.pi,
      Real.cos ((n + 1 : Real) * (alpha - beta))) = 0 := by
  let m : Nat := n + 1
  let z : Int := m
  have hm : 0 < m := by dsimp [m]; omega
  have hz : z ≠ 0 := by dsimp [z]; exact_mod_cast hm.ne'
  have hcosInt : IntervalIntegrable
      (fun beta => Real.cos ((m : Real) * beta)) MeasureTheory.volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hsinInt : IntervalIntegrable
      (fun beta => Real.sin ((m : Real) * beta)) MeasureTheory.volume
      (-Real.pi) Real.pi := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hid (beta : Real) :
      Real.cos ((m : Real) * (alpha - beta)) =
        Real.cos ((m : Real) * alpha) * Real.cos ((m : Real) * beta) +
          Real.sin ((m : Real) * alpha) * Real.sin ((m : Real) * beta) := by
    rw [mul_sub, Real.cos_sub]
  suffices (∫ beta in -Real.pi..Real.pi,
      Real.cos ((m : Real) * (alpha - beta))) = 0 by
    simpa only [m, Nat.cast_add, Nat.cast_one] using this
  rw [intervalIntegral.integral_congr (fun beta _ => hid beta)]
  rw [intervalIntegral.integral_add
    (hcosInt.const_mul _) (hsinInt.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have hcast (beta : Real) : (z : Real) * beta = (m : Real) * beta := by
    dsimp [z]
    norm_cast
  have hcosZero :
      (∫ beta in -Real.pi..Real.pi,
        Real.cos ((m : Real) * beta)) = 0 := by
    calc
      _ = ∫ beta in -Real.pi..Real.pi,
          Real.cos ((z : Real) * beta) := by
        apply intervalIntegral.integral_congr
        intro beta _
        exact congrArg Real.cos (hcast beta).symm
      _ = 0 := by rw [intervalIntegral_cos_int_mul z, if_neg hz]
  have hsinZero :
      (∫ beta in -Real.pi..Real.pi,
        Real.sin ((m : Real) * beta)) = 0 := by
    calc
      _ = ∫ beta in -Real.pi..Real.pi,
          Real.sin ((z : Real) * beta) := by
        apply intervalIntegral.integral_congr
        intro beta _
        exact congrArg Real.sin (hcast beta).symm
      _ = 0 := intervalIntegral_sin_int_mul z
  rw [hcosZero, hsinZero]
  ring

theorem intervalIntegral_shiftedCos_mul_fourierRootDensityTerm
    (lam : Real) (n j : Nat) (alpha : Real) :
    (∫ beta in -Real.pi..Real.pi,
      Real.cos ((n + 1 : Real) * (alpha - beta)) *
        sixVertexFourierRootDensityTerm lam j beta) =
      if n = j then
        Real.pi * Real.cos ((n + 1 : Real) * alpha) /
          Real.cosh ((n + 1 : Real) * lam)
      else 0 := by
  unfold sixVertexFourierRootDensityTerm
  simp_rw [show ∀ beta : Real,
      Real.cos ((n + 1 : Real) * (alpha - beta)) *
          (Real.cos ((j + 1 : Real) * beta) /
            Real.cosh ((j + 1 : Real) * lam)) =
        (Real.cos ((n + 1 : Real) * (alpha - beta)) *
          Real.cos ((j + 1 : Real) * beta)) *
            (1 / Real.cosh ((j + 1 : Real) * lam)) by
      intro beta
      ring]
  rw [intervalIntegral.integral_mul_const,
    show (∫ beta in -Real.pi..Real.pi,
      Real.cos ((n + 1 : Real) * (alpha - beta)) *
        Real.cos ((j + 1 : Real) * beta)) =
      if n + 1 = j + 1 then
        Real.pi * Real.cos ((n + 1 : Real) * alpha) else 0 by
      simpa only [Nat.cast_add, Nat.cast_one] using
        intervalIntegral_cos_nat_mul_sub_mul_cos_nat_mul
          (m := n + 1) (n := j + 1) (by omega) (by omega) alpha]
  by_cases hnj : n = j
  · subst j
    simp
    ring
  · simp [hnj]

end
end StatMech.FrontierD
