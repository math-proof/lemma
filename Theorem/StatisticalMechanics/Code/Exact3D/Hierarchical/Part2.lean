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
import Def.StatisticalMechanics.Code.Exact3D.Hierarchical.Part2


namespace StatMech

namespace Exact3D

theorem hierarchicalLinearization_mem_intervals :
    RatInterval.MatrixMem hierarchicalLinearization hierarchicalLinearizationIntervals := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hierarchicalLinearization, hierarchicalLinearizationIntervals,
      hierarchicalThermalEigenvalue, hierarchicalStableEigenvalue,
      RatInterval.point, RatInterval.MemR]


theorem hierarchicalStableLinearization_mem_intervals :
    RatInterval.MatrixMem hierarchicalStableLinearization
      hierarchicalStableLinearizationIntervals := by
  intro i j
  fin_cases i
  fin_cases j
  simp [hierarchicalStableLinearization, hierarchicalStableLinearizationIntervals,
    hierarchicalStableEigenvalue, RatInterval.point, RatInterval.MemR]


end Exact3D
end StatMech
