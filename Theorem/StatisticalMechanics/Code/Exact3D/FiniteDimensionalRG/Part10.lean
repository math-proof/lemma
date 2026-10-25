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
import Def.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part11


namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplittingExample

theorem stableLinear_mem_enclosure :
    RatInterval.MatrixMem stableLinear stableEnclosure := by
  intro i j
  fin_cases i
  fin_cases j
  norm_num [stableLinear, stableEnclosure, RatInterval.point, RatInterval.MemR]


end FiniteHyperbolicSplittingExample
end Exact3D
end StatMech
