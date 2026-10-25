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
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part20


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace ZeroLinearExample

noncomputable def matrix : Fin 1 → Fin 1 → ℝ :=
  fun _ _ => 0


def intervals : RatInterval.IntervalMatrix 1 1 :=
  fun _ _ => RatInterval.point 0


noncomputable def offset : Fin 1 → ℝ :=
  fun _ => 0


def offsetIntervals : RatInterval.IntervalVector 1 :=
  fun _ => RatInterval.point 0


def offsetQ : Fin 1 → ℚ :=
  fun _ => 0


end ZeroLinearExample
end FiniteContraction
end Exact3D
end StatMech
