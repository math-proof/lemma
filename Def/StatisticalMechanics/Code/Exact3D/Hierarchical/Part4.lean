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
import Structure.StatisticalMechanics.Code.Exact3D.Hierarchical


namespace StatMech

namespace Exact3D

noncomputable def hierarchicalFiniteCertificate : HierarchicalFiniteCertificate where
  linearization := hierarchicalLinearization
  enclosure := hierarchicalLinearizationIntervals
  enclosure_sound := hierarchicalLinearization_mem_intervals
  stable_linearization := hierarchicalStableLinearization
  stable_enclosure := hierarchicalStableLinearizationIntervals
  stable_enclosure_sound := hierarchicalStableLinearization_mem_intervals
  stable_coordinate := hierarchical_stable_abs_lt_one
  stable_row_sum_contraction := hierarchicalStableRowSumContraction


noncomputable def hierarchicalStableBlock : StableBlockWithRemainder 1 :=
  StableBlockWithRemainder.ofLinearRowSum hierarchicalStableLinearization
    hierarchicalStableLinearization_mem_intervals
    hierarchicalStableRowSumContraction


noncomputable def hierarchicalFiniteSplitting : FiniteHyperbolicSplitting 1 :=
  FiniteHyperbolicSplitting.ofLinearStableRowSum
    (n := 1) (thermal := hierarchicalThermalEigenvalue)
    hierarchical_thermal_gt_one hierarchicalStableLinearization
    hierarchicalStableLinearization_mem_intervals
    hierarchicalStableRowSumContraction (by
      norm_num [hierarchicalThermalEigenvalue, hierarchicalStableRowSumContraction])


noncomputable def hierarchicalFiniteSplittingCertificate :
    RGCertificate HierarchicalModel :=
  hierarchicalFiniteSplitting.certificate hierarchicalScale HierarchicalModel


end Exact3D
end StatMech
