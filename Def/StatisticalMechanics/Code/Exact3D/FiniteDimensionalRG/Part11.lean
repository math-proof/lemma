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
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part9


namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplittingExample

noncomputable def stableLinear : Fin 1 → Fin 1 → ℝ :=
  fun _ _ => (1 : ℝ) / 2


def stableEnclosure : RatInterval.IntervalMatrix 1 1 :=
  fun _ _ => RatInterval.point (1 / 2)


end FiniteHyperbolicSplittingExample
end Exact3D
end StatMech
