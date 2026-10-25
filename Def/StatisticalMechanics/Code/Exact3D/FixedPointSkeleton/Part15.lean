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
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part14


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace NonzeroAffineExample

def matrixQ : Fin 1 → Fin 1 → ℚ :=
  fun _ _ => 1 / 2


def offsetQ : Fin 1 → ℚ :=
  fun _ => 1 / 4


def centerQ : Fin 1 → ℚ :=
  fun _ => 1 / 2


noncomputable def matrix : Fin 1 → Fin 1 → ℝ :=
  fun i j => (matrixQ i j : ℝ)


noncomputable def offset : Fin 1 → ℝ :=
  fun i => (offsetQ i : ℝ)


def intervals : RatInterval.IntervalMatrix 1 1 :=
  RatInterval.pointMatrix matrixQ


def offsetIntervals : RatInterval.IntervalVector 1 :=
  RatInterval.pointVector offsetQ


end NonzeroAffineExample
end FiniteContraction
end Exact3D
end StatMech
