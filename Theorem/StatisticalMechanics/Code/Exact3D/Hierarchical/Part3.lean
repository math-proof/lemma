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
import Def.StatisticalMechanics.Code.Exact3D.Hierarchical.Part3


namespace StatMech

namespace Exact3D

theorem hierarchicalStableLinearization_apply_bound (x : Fin 1 → ℝ) (i : Fin 1) :
    |RatInterval.matVec hierarchicalStableLinearization x i| ≤
      ((1 / 2 : ℚ) : ℝ) * RatInterval.supNormVec x := by
  simpa [hierarchicalStableRowSumContraction] using
    hierarchicalStableRowSumContraction.apply_bound
      hierarchicalStableLinearization_mem_intervals x i


end Exact3D
end StatMech
