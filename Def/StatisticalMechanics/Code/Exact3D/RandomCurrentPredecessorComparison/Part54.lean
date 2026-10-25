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
import Structure.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part7
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

noncomputable def OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt.toSourceSectorImageRowsAt
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt
        n Case) :
    OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAt
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
  imageStrictZ := T.imageStrictZ
  weightStrictZ := by
    intro p hrow m
    exact
      weight_ofEdgeFun_le_of_edge_multiplicity_eq
        (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (T.multiplicityStrictZ p hrow m)
  imageDiagY := T.imageDiagY
  weightDiagY := by
    intro p hrow m
    exact
      weight_ofEdgeFun_le_of_edge_multiplicity_eq
        (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (T.multiplicityDiagY p hrow m)
  imageStrictY := T.imageStrictY
  weightStrictY := by
    intro p hrow m
    exact
      weight_ofEdgeFun_le_of_edge_multiplicity_eq
        (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (T.multiplicityStrictY p hrow m)

end Exact3D
end StatMech
