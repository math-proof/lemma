/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.CorrelationLength.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
open MeasureTheory


namespace StatMech

namespace Exact3D

open StatMech.Lattice


theorem Ising3DModel_twoPoint_eq (β : ℝ) (x y : Ising3DSite) :
    TwoPointFunction Ising3DModel β x y = ising3DPlusTwoPoint β x y :=
  rfl


theorem Ising3DModel_betaC_eq :
    Ising3DModel.betaC = Ising.betaC 3 :=
  rfl


theorem ising3DPlusTwoPoint_symm (β : ℝ) (x y : Ising3DSite) :
    ising3DPlusTwoPoint β x y = ising3DPlusTwoPoint β y x := by
  simp [ising3DPlusTwoPoint, mul_comm]


theorem ising3DPlusTwoPoint_self (β : ℝ) (x : Ising3DSite) :
    ising3DPlusTwoPoint β x x = 1 := by
  simp [ising3DPlusTwoPoint, Ising.spin_sq]


theorem ising3DFreeTwoPoint_symm (β : ℝ) (x y : Ising3DSite) :
    ising3DFreeTwoPoint β x y = ising3DFreeTwoPoint β y x := by
  simp [ising3DFreeTwoPoint, mul_comm]


theorem ising3DFreeTwoPoint_self (β : ℝ) (x : Ising3DSite) :
    ising3DFreeTwoPoint β x x = 1 := by
  simp [ising3DFreeTwoPoint, Ising.spin_sq]


theorem abs_spin_mul_spin_le_one (ω : ConfigSpace Ising3DSite) (x y : Ising3DSite) :
    |Ising.spin ω x * Ising.spin ω y| ≤ 1 := by
  rw [abs_mul]
  exact mul_le_one₀ (Ising.abs_spin_le_one ω x) (abs_nonneg _)
    (Ising.abs_spin_le_one ω y)


theorem ising3DPlusTwoPoint_abs_le_one (β : ℝ) (x y : Ising3DSite) :
    |ising3DPlusTwoPoint β x y| ≤ 1 := by
  have hbound :
      ∀ᵐ ω ∂(Ising.plusState 3 β 0 : Measure (ConfigSpace Ising3DSite)),
        ‖Ising.spin ω x * Ising.spin ω y‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using abs_spin_mul_spin_le_one ω x y
  simpa [ising3DPlusTwoPoint, Real.norm_eq_abs] using
    (MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := (Ising.plusState 3 β 0 : Measure (ConfigSpace Ising3DSite))) hbound)


theorem ising3DFreeTwoPoint_abs_le_one (β : ℝ) (x y : Ising3DSite) :
    |ising3DFreeTwoPoint β x y| ≤ 1 := by
  have hbound :
      ∀ᵐ ω ∂(Ising.freeState 3 β 0 : Measure (ConfigSpace Ising3DSite)),
        ‖Ising.spin ω x * Ising.spin ω y‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using abs_spin_mul_spin_le_one ω x y
  simpa [ising3DFreeTwoPoint, Real.norm_eq_abs] using
    (MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := (Ising.freeState 3 β 0 : Measure (ConfigSpace Ising3DSite))) hbound)


theorem Ising3DModel_twoPoint_abs_le_one (β : ℝ) (x y : Ising3DSite) :
    |TwoPointFunction Ising3DModel β x y| ≤ 1 := by
  simpa [Ising3DModel_twoPoint_eq] using ising3DPlusTwoPoint_abs_le_one β x y


theorem Ising3DModel_inverseDecayRate_xAxis_eq (β : ℝ) (n : ℕ) :
    inverseDecayRate Ising3DModel β ising3DOrigin ising3DXAxisRay n =
      plusInverseDecayRateOnXAxis β n := by
  rfl


theorem Ising3DModel_lowerInverseCorrelationLength_xAxis_eq (β : ℝ) :
    lowerInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay =
      plusLowerInverseCorrelationLengthOnXAxis β := by
  rfl


theorem Ising3DModel_upperInverseCorrelationLength_xAxis_eq (β : ℝ) :
    upperInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay =
      plusUpperInverseCorrelationLengthOnXAxis β := by
  rfl


theorem Ising3DModel_liminfCorrelationLength_xAxis_eq (β : ℝ) :
    liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay =
      plusLiminfCorrelationLengthOnXAxis β := by
  rfl

end Exact3D
end StatMech
