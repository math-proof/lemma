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
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part4


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace L1Vector

variable {n : ℕ}


instance instInhabited : Inhabited (L1Vector n) :=
  ⟨ofFun 0⟩


noncomputable instance instMetricSpace (n : ℕ) : MetricSpace (L1Vector n) where
  dist x y := l1Dist x.coord y.coord
  dist_self x := l1Dist_self x.coord
  dist_comm x y := l1Dist_comm x.coord y.coord
  dist_triangle x y z := l1Dist_triangle x.coord y.coord z.coord
  eq_of_dist_eq_zero := by
    intro x y h
    exact L1Vector.ext (eq_of_l1Dist_eq_zero h)


end L1Vector
end FiniteContraction
end Exact3D
end StatMech
