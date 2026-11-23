/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.UniformSpace.Pi
public import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
public import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part2

public section

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
