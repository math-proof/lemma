/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12
import Structure.StatisticalMechanics.Code.Exact3D.FinitePlusTailCone


namespace StatMech

namespace Exact3D

namespace FinitePlusTailHyperbolicSplitting

variable {n : ℕ} {α : Type*}


abbrev State (n : ℕ) (α : Type*) :=
  ℝ × FinitePlusTailState n α


end FinitePlusTailHyperbolicSplitting
end Exact3D
end StatMech
