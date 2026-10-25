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
import Def.StatisticalMechanics.Code.Exact3D.Hierarchical


namespace StatMech

namespace Exact3D

theorem hierarchical_thermal_gt_one : 1 < hierarchicalThermalEigenvalue := by
  norm_num [hierarchicalThermalEigenvalue]

theorem hierarchical_stable_abs_lt_one : |hierarchicalStableEigenvalue| < 1 := by
  norm_num [hierarchicalStableEigenvalue]


end Exact3D
end StatMech
