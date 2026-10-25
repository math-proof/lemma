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
import Def.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG


namespace StatMech

namespace Exact3D

namespace IntervalLipschitzConstant

theorem upper_nonneg (L : IntervalLipschitzConstant) : 0 ≤ L.upper :=
  le_trans L.nonnegative L.interval.lower_le_upper


end IntervalLipschitzConstant
end Exact3D
end StatMech
