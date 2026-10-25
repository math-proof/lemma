/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Structure.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockBounds

variable {n : ℕ} {α : Type*}


noncomputable def map (B : FinitePlusTailBlockBounds n α) :
    FinitePlusTailState n α → FinitePlusTailState n α :=
  fun x => { finite := B.finiteMap x, tail := B.tailMap x }

end FinitePlusTailBlockBounds
end Exact3D
end StatMech
