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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part143
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


abbrev BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule :
    Type :=
  ResidualThresholdShellBudget15AggregateShareSchedule

set_option linter.style.longLine false in


abbrev BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule :
    Type :=
  ResidualThresholdShellBudget15AggregateShareSchedule

set_option linter.style.longLine false in


abbrev BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSummandBudgetSchedule :
    Type :=
  ResidualThresholdShellBudget15AggregateShareSchedule

set_option linter.style.longLine false in


abbrev BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule :
    Type :=
  ResidualThresholdShellBudget15AggregateShareSchedule

set_option linter.style.longLine false in


abbrev BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostMultiplicityBudgetSchedule :
    Type :=
  ResidualThresholdShellBudget15AggregateShareSchedule

set_option linter.style.longLine false in


abbrev BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryVertexBudgetSchedule :
    Type :=
  ResidualThresholdShellBudget15AggregateShareSchedule

set_option linter.style.longLine false in


abbrev BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeMultiplicityBudgetSchedule :
    Type :=
  ResidualThresholdShellBudget15AggregateShareSchedule

end Exact3D
end StatMech
