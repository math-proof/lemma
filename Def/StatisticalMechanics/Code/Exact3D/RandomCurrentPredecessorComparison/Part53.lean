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
import Structure.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part6
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

noncomputable def OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAt.toSourceSectorInjectionRowsAt
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAt
        β n Case) :
    OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorInjectionRowsAt
      β n Case where
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
  sourceStrictZ := by
    intro p hrow m
    exact (T.imageStrictZ p hrow m).toSourceSectorInjection
  weightStrictZ := T.weightStrictZ
  sourceDiagY := by
    intro p hrow m
    exact (T.imageDiagY p hrow m).toSourceSectorInjection
  weightDiagY := T.weightDiagY
  sourceStrictY := by
    intro p hrow m
    exact (T.imageStrictY p hrow m).toSourceSectorInjection
  weightStrictY := T.weightStrictY


end Exact3D
end StatMech
