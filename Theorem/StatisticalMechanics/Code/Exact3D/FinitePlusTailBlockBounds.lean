/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockBounds

variable {n : ℕ} {α : Type*}


@[simp] theorem map_finite
    (B : FinitePlusTailBlockBounds n α) (x : FinitePlusTailState n α) :
    (B.map x).finite = B.finiteMap x :=
  rfl

@[simp] theorem map_tail
    (B : FinitePlusTailBlockBounds n α) (x : FinitePlusTailState n α) :
    (B.map x).tail = B.tailMap x :=
  rfl


theorem map_finite_bound
    (B : FinitePlusTailBlockBounds n α) (x y : FinitePlusTailState n α) :
    (B.map x).finiteDist (B.map y) ≤
      B.finiteToFinite * x.finiteDist y +
        B.tailToFinite * x.tailDist y := by
  simpa [map, FinitePlusTailState.finiteDist] using B.finite_bound x y


theorem map_tail_bound
    (B : FinitePlusTailBlockBounds n α) (x y : FinitePlusTailState n α) :
    (B.map x).tailDist (B.map y) ≤
      B.finiteToTail * x.finiteDist y +
        B.tailToTail * x.tailDist y := by
  simpa [map, FinitePlusTailState.tailDist] using B.tail_bound x y


end FinitePlusTailBlockBounds
end Exact3D
end StatMech
