/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part15
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
import Def.StatisticalMechanics.Code.Exact3D.Hierarchical.Part4


namespace StatMech

namespace Exact3D

theorem hierarchicalFiniteSplitting_predictedExponent_eq :
    hierarchicalFiniteSplittingCertificate.predictedExponent = hierarchicalNu := by
  rfl


theorem hierarchicalFiniteSplitting_fixedPointEnclosure :
    hierarchicalFiniteSplittingCertificate.FixedPointEnclosure :=
  hierarchicalFiniteSplitting.certificate_fixedPointEnclosure hierarchicalScale
    HierarchicalModel


theorem hierarchical_logSlope_eq_nu_of_mem {β : ℝ} (hβ : β ∈ Set.Ioo (-1) 0) :
    logSlope HierarchicalModel hierarchicalCorrelationLength β = hierarchicalNu := by
  have hβ_pos : 0 < -β := by linarith [hβ.2]
  have hβ_lt_one : -β < 1 := by linarith [hβ.1]
  have hlog_ne : Real.log (-β) ≠ 0 :=
    (Real.log_neg hβ_pos hβ_lt_one).ne
  have hlogβ_ne : Real.log β ≠ 0 := by
    simpa [Real.log_neg_eq_log] using hlog_ne
  simp [logSlope, HierarchicalModel, hierarchicalCorrelationLength]
  field_simp [hlogβ_ne]


theorem hierarchical_hasCriticalNu :
    HasCriticalNu HierarchicalModel hierarchicalCorrelationLength hierarchicalNu := by
  unfold HasCriticalNu
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 0 by norm_num)] with β hβ
  exact (hierarchical_logSlope_eq_nu_of_mem hβ).symm


theorem hierarchical_bridge_via_exact_power :
    hierarchicalCertificate.RGToExponentBridge hierarchicalCorrelationLength := by
  refine hierarchicalCertificate.rgToExponentBridge_of_exact_power_on_Ioo
    hierarchicalCorrelationLength 1 (by norm_num) ?_
  intro β hβ
  simp [hierarchicalCorrelationLength, hierarchicalNu, HierarchicalModel]


theorem hierarchicalFiniteSplitting_bridge :
    hierarchicalFiniteSplittingCertificate.RGToExponentBridge
      hierarchicalCorrelationLength := by
  simpa [RGCertificate.RGToExponentBridge,
    hierarchicalFiniteSplitting_predictedExponent_eq] using hierarchical_hasCriticalNu


theorem hierarchicalFiniteSplittingCertificate_valid :
    hierarchicalFiniteSplittingCertificate.Valid hierarchicalCorrelationLength := by
  refine ⟨trivial, trivial, hierarchicalFiniteSplitting_fixedPointEnclosure,
    ?_, ?_, trivial, hierarchicalFiniteSplitting_bridge⟩
  · exact
      hierarchicalFiniteSplittingCertificate.linearizationEnclosure_of_thermal_gt_one
  · exact hierarchicalFiniteSplittingCertificate.hyperbolicSplitting_of_thermal_gt_one


theorem hierarchicalCertificate_valid :
    hierarchicalCertificate.Valid hierarchicalCorrelationLength := by
  refine ⟨trivial, trivial, ?_, ?_, ?_, trivial, ?_⟩
  · exact hierarchicalFixedPointData.fixedPoint_eq
  · exact hierarchicalCertificate.linearizationEnclosure_of_thermal_gt_one
  · exact hierarchicalCertificate.hyperbolicSplitting_of_thermal_gt_one
  · exact hierarchical_bridge_via_exact_power


theorem hierarchical_hasCriticalNu_eq_log_scale_div_log_thermal :
    HasCriticalNu HierarchicalModel hierarchicalCorrelationLength
      (Real.log hierarchicalCertificate.scale.toReal /
        Real.log hierarchicalCertificate.thermalEigenvalue) := by
  simpa [RGCertificate.predictedExponent, predictedNu] using
    hierarchicalCertificate_valid.hasCriticalNu

end Exact3D
end StatMech
