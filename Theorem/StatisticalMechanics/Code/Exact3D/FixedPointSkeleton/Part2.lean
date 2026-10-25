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
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part2


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

theorem lipschitzWithConstant_mono {n : ℕ}
    {F : (Fin n → ℝ) → Fin n → ℝ} {c c' : ℝ}
    (hLip : LipschitzWithConstant F c) (hc : c ≤ c') :
    LipschitzWithConstant F c' := by
  intro x y
  exact le_trans (hLip x y)
    (mul_le_mul_of_nonneg_right hc (l1Dist_nonneg x y))


end FiniteContraction
end Exact3D
end StatMech
