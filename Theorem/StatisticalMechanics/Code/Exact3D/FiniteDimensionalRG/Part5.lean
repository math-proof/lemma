/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Def.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part5


namespace StatMech

namespace Exact3D

namespace StableBlockWithRemainder

theorem step_mem_thermalStableCone_of_l1StepConstant_le_abs_thermal
    {n : ℕ} (S : StableBlockWithRemainder n)
    {thermal η t : ℝ} {s : Fin n → ℝ}
    (hη : 0 ≤ η)
    (hdom : S.l1StepConstant ≤ |thermal|)
    (hs : ThermalStableCone η t s) :
    ThermalStableCone η (thermal * t) (S.step s) := by
  have hK_nonneg : 0 ≤ S.l1StepConstant := S.l1StepConstant_nonneg
  have hcone_rhs_nonneg : 0 ≤ η * |t| :=
    mul_nonneg hη (abs_nonneg t)
  calc
    RatInterval.supNormVec (S.step s)
        ≤ S.l1StepConstant * RatInterval.supNormVec s :=
      S.step_supNormVec_bound s
    _ ≤ S.l1StepConstant * (η * |t|) :=
      mul_le_mul_of_nonneg_left hs hK_nonneg
    _ ≤ |thermal| * (η * |t|) :=
      mul_le_mul_of_nonneg_right hdom hcone_rhs_nonneg
    _ = η * |thermal * t| := by
      rw [abs_mul]
      ring


theorem iterate_mem_thermalStableCone_of_l1StepConstant_le_abs_thermal
    {n : ℕ} (S : StableBlockWithRemainder n)
    {thermal η t : ℝ} {s : Fin n → ℝ}
    (hη : 0 ≤ η)
    (hdom : S.l1StepConstant ≤ |thermal|)
    (hs : ThermalStableCone η t s) (k : ℕ) :
    ThermalStableCone η (thermal ^ k * t) (S.iterate k s) := by
  induction k with
  | zero =>
      simpa [iterate] using hs
  | succ k ih =>
      have hstep :=
        S.step_mem_thermalStableCone_of_l1StepConstant_le_abs_thermal
          hη hdom ih
      simpa [iterate, pow_succ', mul_assoc] using hstep

end StableBlockWithRemainder
end Exact3D
end StatMech
