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
import Instance.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace L1Vector

variable {n : ℕ}


def equivFun (n : ℕ) : L1Vector n ≃ (Fin n → ℝ) where
  toFun x := x.coord
  invFun := ofFun
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    rfl


end L1Vector
end FiniteContraction
end Exact3D
end StatMech
