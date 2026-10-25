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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part131
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregatePolynomialBoundaryBudget
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    ℝ :=
  let cardBudget := (Ω.card : ℝ)
  let sourceCardBudget :=
    ∑ m ∈ Ω, ((finiteBoundaryGhostSourceSector m).card : ℝ)
  let edgeBudget :=
    ∑ m ∈ Ω,
      ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
  let boundaryCard := 26 * (n : ℝ) ^ 2
  cardBudget *
    (sourceCardBudget * (boundaryCard * edgeBudget) *
      (boundaryCard * edgeBudget))

end Exact3D
end StatMech
