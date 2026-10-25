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
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part9


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace ClosedBallContractionCertificate

variable {n : ℕ} {F : (Fin n → ℝ) → Fin n → ℝ}


def with_larger_radius (C : ClosedBallContractionCertificate F)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    ClosedBallContractionCertificate F where
  center := C.center
  radius := radius'
  c := C.c
  c_nonneg := C.c_nonneg
  c_lt_one := C.c_lt_one
  radius_nonneg := le_trans C.radius_nonneg hradius
  lipschitz := C.lipschitz
  residual_bound := by
    exact le_trans C.residual_bound
      (mul_le_mul_of_nonneg_left hradius (sub_nonneg.mpr C.c_lt_one.le))

end ClosedBallContractionCertificate
end FiniteContraction
end Exact3D
end StatMech
