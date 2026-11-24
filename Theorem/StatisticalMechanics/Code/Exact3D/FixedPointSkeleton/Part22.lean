module
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.UniformSpace.Pi
public import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
public import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part22


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

namespace ZeroLinearExample

theorem residual_mem :
    RatInterval.VectorMem
      (fun i => RatInterval.matVec matrix (0 : Fin 1 → ℝ) i -
        (0 : Fin 1 → ℝ) i)
      residualIntervals := by
  intro i
  fin_cases i
  norm_num [matrix, residualIntervals, RatInterval.matVec, RatInterval.point,
    RatInterval.MemR]


end ZeroLinearExample
end FiniteContraction
end Exact3D
end StatMech
