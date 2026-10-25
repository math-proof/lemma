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
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part8


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

structure ClosedBallContractionCertificate {n : ℕ}
    (F : (Fin n → ℝ) → Fin n → ℝ) where
  center : Fin n → ℝ
  radius : ℝ
  c : ℝ
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1
  radius_nonneg : 0 ≤ radius
  lipschitz : LipschitzWithConstant F c
  residual_bound : l1Dist (F center) center ≤ (1 - c) * radius


end FiniteContraction
end Exact3D
end StatMech
