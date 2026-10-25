/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part126
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

def BoundaryCrossingCapUpperBoundPositiveSubcritical
    (capBound : BoundaryCrossingCapBound) : Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
          boundaryCrossingCap n Ωnz ≤ capBound β H n Ωnz


def BoundaryCrossingCapBoundNonnegativePositiveSubcritical
    (capBound : BoundaryCrossingCapBound) : Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
          0 ≤ capBound β H n Ωnz


def BoundaryCrossingCapBoundLePositiveSubcritical
    (capSmall capLarge : BoundaryCrossingCapBound) : Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
          capSmall β H n Ωnz ≤ capLarge β H n Ωnz

end Exact3D
end StatMech
