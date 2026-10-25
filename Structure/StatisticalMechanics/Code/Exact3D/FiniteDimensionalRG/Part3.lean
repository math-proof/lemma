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
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part5


namespace StatMech

namespace Exact3D

structure FiniteHyperbolicSplitting (n : ℕ) where
  thermal : ℝ
  thermal_gt_one : 1 < thermal
  stable : StableBlockWithRemainder n
  stable_dominated : stable.l1StepConstant ≤ |thermal|

end Exact3D
end StatMech
