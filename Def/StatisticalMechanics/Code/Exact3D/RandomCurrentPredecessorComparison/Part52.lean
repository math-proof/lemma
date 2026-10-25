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
import Structure.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part5
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

def OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorInjectionRowsAt.toReindexRowsAt
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorInjectionRowsAt
        β n Case) :
    OrderedWedgePredecessorEdgeCopyCollapsedReindexRowsAt β n Case where
  rows := T.rows
  rowPred := T.rowPred
  classifyStrictZ := T.classifyStrictZ
  classifyDiagY := T.classifyDiagY
  classifyStrictY := T.classifyStrictY
  coversStrictZ := T.coversStrictZ
  coversDiagY := T.coversDiagY
  coversStrictY := T.coversStrictY
  mapStrictZ := T.mapStrictZ
  mapStrictZ_injective := T.mapStrictZ_injective
  mapDiagY := T.mapDiagY
  mapDiagY_injective := T.mapDiagY_injective
  mapStrictY := T.mapStrictY
  mapStrictY_injective := T.mapStrictY_injective
  soundStrictZ := by
    intro p hrow m
    exact
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorInjection_of_weight_le
        m (T.mapStrictZ p m) hβ (T.sourceStrictZ p hrow m)
        (T.weightStrictZ p hrow m)
  soundDiagY := by
    intro p hrow m
    exact
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorInjection_of_weight_le
        m (T.mapDiagY p m) hβ (T.sourceDiagY p hrow m)
        (T.weightDiagY p hrow m)
  soundStrictY := by
    intro p hrow m
    exact
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorInjection_of_weight_le
        m (T.mapStrictY p m) hβ (T.sourceStrictY p hrow m)
        (T.weightStrictY p hrow m)


end Exact3D
end StatMech
