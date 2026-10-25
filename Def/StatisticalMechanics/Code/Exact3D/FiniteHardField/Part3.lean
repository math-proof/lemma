/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteHardField.Part2
open Filter
open scoped BigOperators Topology


namespace StatMech

namespace Exact3D

noncomputable def countHardFieldFactor {α : Type*} (penalty : α → ℕ)
    (scale H : ℝ) (a : α) : ℝ :=
  Real.exp (-(scale * H * (penalty a : ℝ)))


noncomputable def countHardFieldLimitFactor {α : Type*}
    (penalty : α → ℕ) (a : α) : ℝ :=
  if penalty a = 0 then 1 else 0


end Exact3D
end StatMech
