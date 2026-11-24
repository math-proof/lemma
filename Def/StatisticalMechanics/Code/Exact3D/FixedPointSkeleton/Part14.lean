module
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.UniformSpace.Pi
public import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part13


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

def zeroMap_closedBallContractionCertificate {n : ℕ} {radius : ℝ}
    (hradius : 0 ≤ radius) :
    ClosedBallContractionCertificate (@zeroMap n) where
  center := 0
  radius := radius
  c := 0
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  radius_nonneg := hradius
  lipschitz := zeroMap_lipschitz_zero
  residual_bound := by
    simpa [l1Dist, zeroMap, RatInterval.supNormVec] using hradius


end FiniteContraction
end Exact3D
end StatMech
