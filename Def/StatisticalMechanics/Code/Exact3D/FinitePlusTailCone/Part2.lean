/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12
import Abbrev.StatisticalMechanics.Code.Exact3D.FinitePlusTailCone


namespace StatMech

namespace Exact3D

namespace FinitePlusTailHyperbolicSplitting

variable {n : ℕ} {α : Type*}


def origin : State n α :=
  (0, FinitePlusTailState.origin)


noncomputable def step (H : FinitePlusTailHyperbolicSplitting n α)
    (x : State n α) : State n α :=
  (H.thermal * x.1, H.stable.map x.2)


noncomputable def iterate (H : FinitePlusTailHyperbolicSplitting n α) :
    ℕ → State n α → State n α
  | 0, x => x
  | k + 1, x => H.step (H.iterate k x)


end FinitePlusTailHyperbolicSplitting
end Exact3D
end StatMech
