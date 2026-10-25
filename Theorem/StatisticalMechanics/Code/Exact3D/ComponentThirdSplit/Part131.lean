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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part144
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_eventually_eq_exactPolynomialBoundaryBudget :
    ∀ᶠ n in atTop,
      ∀ Ω : Finset
        (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
        boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
            n Ω =
          boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
            n Ω := by
  filter_upwards [boxBoundaryCard3_eventually_eq] with n hboundary
  intro Ω
  simp [
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget,
    hboundary]

end Exact3D
end StatMech
