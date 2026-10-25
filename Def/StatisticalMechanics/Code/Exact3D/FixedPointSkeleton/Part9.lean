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
import Structure.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part2


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

def closedBallContractionCertificate_of_residualBound_and_lipschitz {n : ℕ}
    (F : (Fin n → ℝ) → Fin n → ℝ) {c radius residualBound : ℝ}
    (center : Fin n → ℝ)
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) (hradius : 0 ≤ radius)
    (hLip : LipschitzWithConstant F c)
    (hresidual : l1Dist (F center) center ≤ residualBound)
    (hresidualBound : residualBound ≤ (1 - c) * radius) :
    ClosedBallContractionCertificate F where
  center := center
  radius := radius
  c := c
  c_nonneg := hc_nonneg
  c_lt_one := hc_lt_one
  radius_nonneg := hradius
  lipschitz := hLip
  residual_bound := le_trans hresidual hresidualBound

end FiniteContraction
end Exact3D
end StatMech
