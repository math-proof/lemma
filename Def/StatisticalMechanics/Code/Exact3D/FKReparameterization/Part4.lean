/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Reparameterization.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part3


namespace StatMech

namespace Exact3D

namespace FKReparameterization

set_option linter.style.longLine false in


noncomputable def expLogUpperComparisonPrefactor
    (lo hi k : ℝ) : ℝ :=
  if 0 ≤ k then
    Real.exp (k * Real.log hi)
  else
    Real.exp (k * Real.log lo)

end FKReparameterization
end Exact3D
end StatMech
