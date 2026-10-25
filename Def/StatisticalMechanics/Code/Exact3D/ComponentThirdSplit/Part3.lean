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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part3
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
                β H n Ω v ≤
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                β H n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v

set_option linter.style.longLine false in


def BoundaryVertexDecrementedSourceProfileMajorizationWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
                β H n Ωnz v ≤
              finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
                β H n Ωnz v

end Exact3D
end StatMech
