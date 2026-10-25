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
import Def.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part16


namespace StatMech

namespace Exact3D

namespace TwoCoordinateRGData

theorem thermal_pos (D : TwoCoordinateRGData) : 0 < D.thermal :=
  lt_trans zero_lt_one D.thermal_gt_one


theorem abs_thermal_eq (D : TwoCoordinateRGData) : |D.thermal| = D.thermal :=
  abs_of_pos D.thermal_pos


theorem stable_abs_le_thermal_abs (D : TwoCoordinateRGData) :
    |D.stable| ≤ |D.thermal| := by
  rw [D.abs_thermal_eq]
  exact (lt_trans D.stable_abs_lt_one D.thermal_gt_one).le


theorem thermalCone_step {D : TwoCoordinateRGData} {K : ℝ} (hK : 0 ≤ K)
    {x : ℝ × ℝ} (hx : D.thermalCone K x) :
    D.thermalCone K (D.rgMap.map x) := by
  unfold thermalCone
  change |D.stable * x.2| ≤ K * |D.thermal * x.1|
  calc
    |D.stable * x.2| = |D.stable| * |x.2| := abs_mul _ _
    _ ≤ |D.stable| * (K * |x.1|) := by
      exact mul_le_mul_of_nonneg_left hx (abs_nonneg D.stable)
    _ = K * (|D.stable| * |x.1|) := by ring
    _ ≤ K * (|D.thermal| * |x.1|) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right D.stable_abs_le_thermal_abs
          (abs_nonneg x.1)) hK
    _ = K * |D.thermal * x.1| := by
      rw [abs_mul]


theorem thermalCone_iterate {D : TwoCoordinateRGData} {K : ℝ} (hK : 0 ≤ K)
    {x : ℝ × ℝ} (hx : D.thermalCone K x) (n : ℕ) :
    D.thermalCone K (D.iterate n x) := by
  induction n with
  | zero =>
      simpa [iterate] using hx
  | succ _ ih =>
      exact thermalCone_step hK ih


theorem exactScaleObservable_eq_power (D : TwoCoordinateRGData) (β : ℝ) :
    D.exactScaleObservable β =
      Real.exp (-D.certificate.predictedExponent *
        Real.log (D.model.betaC - β)) := by
  simp [exactScaleObservable, nu, model]


theorem bridge (D : TwoCoordinateRGData) :
    D.certificate.RGToExponentBridge D.exactScaleObservable := by
  refine D.certificate.rgToExponentBridge_of_exact_power_on_Ioo
    D.exactScaleObservable 1 (by norm_num) ?_
  intro β _hβ
  exact D.exactScaleObservable_eq_power β


theorem certificate_valid (D : TwoCoordinateRGData) :
    D.certificate.Valid D.exactScaleObservable := by
  refine ⟨trivial, trivial, ?_, ?_, ?_, trivial, ?_⟩
  · exact D.fixedPointData.fixedPoint_eq
  · exact D.certificate.linearizationEnclosure_of_thermal_gt_one
  · exact D.certificate.hyperbolicSplitting_of_thermal_gt_one
  · exact D.bridge


theorem hasCriticalNu_eq_predicted (D : TwoCoordinateRGData) :
    HasCriticalNu D.model D.exactScaleObservable D.certificate.predictedExponent :=
  D.certificate_valid.hasCriticalNu

end TwoCoordinateRGData
end Exact3D
end StatMech
