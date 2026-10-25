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
import Theorem.StatisticalMechanics.Code.Exact3D.Hierarchical.Part3


namespace StatMech

namespace Exact3D

structure HierarchicalFiniteCertificate where
  linearization : Fin 2 → Fin 2 → ℝ
  enclosure : RatInterval.IntervalMatrix 2 2
  enclosure_sound : RatInterval.MatrixMem linearization enclosure
  stable_linearization : Fin 1 → Fin 1 → ℝ
  stable_enclosure : RatInterval.IntervalMatrix 1 1
  stable_enclosure_sound : RatInterval.MatrixMem stable_linearization stable_enclosure
  stable_coordinate : |hierarchicalStableEigenvalue| < 1
  stable_row_sum_contraction : RatInterval.RowSumContraction stable_enclosure


end Exact3D
end StatMech
