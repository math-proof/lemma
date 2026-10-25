/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Reparameterization.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2


namespace StatMech

namespace Exact3D

noncomputable def ParameterModel (c : ℝ) : CriticalModel Unit where
  betaC := c
  twoPoint := fun _ _ _ => 0

end Exact3D
end StatMech
