/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part63
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

structure OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorInjectionRowsAtPackage
    (β : ℝ) (n : ℕ) : Type 1 where
  Case : Type
  inst : DecidableEq Case
  table :
    @OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorInjectionRowsAt
      β n Case inst
  rows_sound :
    ∀ c, c ∈ table.rows → table.rowPred c


end Exact3D
end StatMech
