/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part14


namespace StatMech

namespace Exact3D

namespace TwoCoordinateRGData

def thermalCone (_D : TwoCoordinateRGData) (K : ℝ) (x : ℝ × ℝ) : Prop :=
  |x.2| ≤ K * |x.1|


end TwoCoordinateRGData
end Exact3D
end StatMech
