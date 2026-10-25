/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailCone.Part2


namespace StatMech

namespace Exact3D

namespace FinitePlusTailHyperbolicSplitting

variable {n : ℕ} {α : Type*}


def cone (_H : FinitePlusTailHyperbolicSplitting n α)
    (η : ℝ) (x : State n α) : Prop :=
  FinitePlusTailState.ThermalStableCone η x.1 x.2


end FinitePlusTailHyperbolicSplitting
end Exact3D
end StatMech
