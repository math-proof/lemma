/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Reparameterization.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part3


namespace StatMech

namespace Exact3D

namespace FKReparameterization

theorem pOfBetaCriticalDistanceComparableWindow_pos (βc : ℝ) :
    0 < pOfBetaCriticalDistanceComparableWindow βc := by
  exact (Classical.choose_spec
    (exists_pOfBeta_criticalDistance_comparable_Ioo_left βc)).1

set_option linter.style.longLine false in


theorem pOfBeta_criticalDistance_comparable_of_mem_Ioo_left
    {βc β : ℝ}
    (hβ :
      β ∈ Set.Ioo
        (βc - pOfBetaCriticalDistanceComparableWindow βc) βc) :
    Real.exp (-2 * βc) * (βc - β) ≤
        IsingFK.pOfBeta βc - IsingFK.pOfBeta β ∧
      IsingFK.pOfBeta βc - IsingFK.pOfBeta β ≤
        (3 * Real.exp (-2 * βc)) * (βc - β) := by
  exact (Classical.choose_spec
    (exists_pOfBeta_criticalDistance_comparable_Ioo_left βc)).2 β hβ

set_option linter.style.longLine false in


theorem exp_log_lower_power_transfer_of_mul_le
    {lo d p k δ : ℝ}
    (hlo : 0 < lo) (hd : 0 < d) (hdlt : d < 1)
    (hk : 0 ≤ k) (hδ : 0 ≤ δ) (hcomp : lo * d ≤ p) :
    Real.exp (k * Real.log lo) *
        Real.exp ((k + δ) * Real.log d) ≤
      Real.exp (k * Real.log p) := by
  rw [← Real.exp_add]
  rw [Real.exp_le_exp]
  have hlogcomp : Real.log (lo * d) ≤ Real.log p :=
    Real.log_le_log (mul_pos hlo hd) hcomp
  have hlogmul : Real.log (lo * d) = Real.log lo + Real.log d := by
    rw [Real.log_mul hlo.ne' hd.ne']
  have hlogcomp' : Real.log lo + Real.log d ≤ Real.log p := by
    simpa [hlogmul] using hlogcomp
  have hmul : k * (Real.log lo + Real.log d) ≤ k * Real.log p :=
    mul_le_mul_of_nonneg_left hlogcomp' hk
  have hlogd_nonpos : Real.log d ≤ 0 :=
    Real.log_nonpos hd.le hdlt.le
  have hdelta : δ * Real.log d ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hδ hlogd_nonpos
  calc
    k * Real.log lo + (k + δ) * Real.log d =
        k * (Real.log lo + Real.log d) + δ * Real.log d := by ring
    _ ≤ k * Real.log p + 0 := add_le_add hmul hdelta
    _ = k * Real.log p := by ring

set_option linter.style.longLine false in


theorem exp_log_lower_power_transfer_no_slack_of_mul_le
    {lo d p k : ℝ}
    (hlo : 0 < lo) (hd : 0 < d)
    (hk : 0 ≤ k) (hcomp : lo * d ≤ p) :
    Real.exp (k * Real.log lo) *
        Real.exp (k * Real.log d) ≤
      Real.exp (k * Real.log p) := by
  rw [← Real.exp_add]
  rw [Real.exp_le_exp]
  have hlogcomp : Real.log (lo * d) ≤ Real.log p :=
    Real.log_le_log (mul_pos hlo hd) hcomp
  have hlogmul : Real.log (lo * d) = Real.log lo + Real.log d := by
    rw [Real.log_mul hlo.ne' hd.ne']
  have hlogcomp' : Real.log lo + Real.log d ≤ Real.log p := by
    simpa [hlogmul] using hlogcomp
  calc
    k * Real.log lo + k * Real.log d =
        k * (Real.log lo + Real.log d) := by ring
    _ ≤ k * Real.log p := mul_le_mul_of_nonneg_left hlogcomp' hk

set_option linter.style.longLine false in

theorem exp_log_power_slack_le_of_lt_one
    {d k δ : ℝ} (hd : 0 < d) (hdlt : d < 1) (hδ : 0 ≤ δ) :
    Real.exp ((k + δ) * Real.log d) ≤
      Real.exp (k * Real.log d) := by
  rw [Real.exp_le_exp]
  have hlogd_nonpos : Real.log d ≤ 0 :=
    Real.log_nonpos hd.le hdlt.le
  have hdelta : δ * Real.log d ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hδ hlogd_nonpos
  calc
    (k + δ) * Real.log d =
        k * Real.log d + δ * Real.log d := by ring
    _ ≤ k * Real.log d + 0 := add_le_add le_rfl hdelta
    _ = k * Real.log d := by ring

end FKReparameterization
end Exact3D
end StatMech
