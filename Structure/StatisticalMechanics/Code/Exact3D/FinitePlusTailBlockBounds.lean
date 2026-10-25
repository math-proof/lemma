/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4


namespace StatMech

namespace Exact3D

structure FinitePlusTailBlockBounds (n : ℕ) (α : Type*) where
  finiteMap : FinitePlusTailState n α → Fin n → ℝ
  tailMap : FinitePlusTailState n α → SummableTail α
  finiteToFinite : ℝ
  tailToFinite : ℝ
  finiteToTail : ℝ
  tailToTail : ℝ
  finiteToFinite_nonneg : 0 ≤ finiteToFinite
  tailToFinite_nonneg : 0 ≤ tailToFinite
  finiteToTail_nonneg : 0 ≤ finiteToTail
  tailToTail_nonneg : 0 ≤ tailToTail
  finite_bound :
    ∀ x y,
      FiniteContraction.l1Dist (finiteMap x) (finiteMap y) ≤
        finiteToFinite * x.finiteDist y + tailToFinite * x.tailDist y
  tail_bound :
    ∀ x y,
      (tailMap x).dist (tailMap y) ≤
        finiteToTail * x.finiteDist y + tailToTail * x.tailDist y

end Exact3D
end StatMech
