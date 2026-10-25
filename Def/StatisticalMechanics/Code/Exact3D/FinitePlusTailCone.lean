/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12


namespace StatMech

namespace Exact3D

namespace FinitePlusTailState

variable {n : ℕ} {α : Type*}


def origin : FinitePlusTailState n α where
  finite := 0
  tail := 0


noncomputable def mixedNorm (x : FinitePlusTailState n α) : ℝ :=
  x.dist (origin : FinitePlusTailState n α)


def ThermalStableCone (η t : ℝ) (s : FinitePlusTailState n α) : Prop :=
  mixedNorm s ≤ η * |t|


end FinitePlusTailState
end Exact3D
end StatMech
