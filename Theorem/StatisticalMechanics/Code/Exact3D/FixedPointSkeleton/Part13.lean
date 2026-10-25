/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.UniformSpace.Pi
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part13


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

theorem zeroMap_lipschitz_zero {n : ℕ} :
    LipschitzWithConstant (@zeroMap n) 0 := by
  intro x y
  simp [l1Dist, zeroMap, RatInterval.supNormVec]


end FiniteContraction
end Exact3D
end StatMech
