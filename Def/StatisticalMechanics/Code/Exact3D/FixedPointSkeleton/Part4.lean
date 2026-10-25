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
import Structure.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace L1Vector

variable {n : ℕ}


def ofFun (x : Fin n → ℝ) : L1Vector n :=
  ⟨x⟩

end L1Vector
end FiniteContraction
end Exact3D
end StatMech
