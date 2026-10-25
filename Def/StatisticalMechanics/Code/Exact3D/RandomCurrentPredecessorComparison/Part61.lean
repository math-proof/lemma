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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part67
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

noncomputable def OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage.toSourceSectorImageRowsAtPackage
    {β : ℝ} {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage
        n) :
    OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAtPackage
      β n := by
  letI := P.inst
  exact {
    Case := P.Case
    inst := P.inst
    table :=
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt.toSourceSectorImageRowsAt
        (β := β) P.table
    rows_sound := P.rows_sound
  }


noncomputable def OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAtPackage.toSourceSectorImageRowsAtPackage
    {β : ℝ} {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAtPackage
        n) :
    OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAtPackage
      β n := by
  letI := P.inst
  exact {
    Case := P.Case
    inst := P.inst
    table :=
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAt.toSourceSectorImageRowsAt
        (β := β) P.table
    rows_sound := P.rows_sound
  }


noncomputable def OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAtPackage.toSourceSectorImageEdgeRelabelRowsAtPackage
    {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAtPackage
        n) :
    OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAtPackage
      n := by
  letI := P.inst
  exact {
    Case := P.Case
    inst := P.inst
    table :=
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt.toSourceSectorImageEdgeRelabelRowsAt
        P.table
    rows_sound := P.rows_sound
  }


noncomputable def OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAtPackage.toSourceSectorImageRowsAtPackage
    {β : ℝ} {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAtPackage
        n) :
    OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAtPackage
      β n :=
  OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAtPackage.toSourceSectorImageRowsAtPackage
    (β := β)
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAtPackage.toSourceSectorImageEdgeRelabelRowsAtPackage
      P)


noncomputable def OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage.toSourceSectorImageEdgeVertexRelabelRowsAtPackage
    {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n) :
    OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAtPackage
      n := by
  letI := P.inst
  exact {
    Case := P.Case
    inst := P.inst
    table :=
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt.of_maps_origin_endpoint
        P.table
    rows_sound := P.rows_sound
  }


noncomputable def OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage.toSourceSectorImageEdgeRelabelRowsAtPackage
    {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n) :
    OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAtPackage
      n :=
  OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAtPackage.toSourceSectorImageEdgeRelabelRowsAtPackage
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage.toSourceSectorImageEdgeVertexRelabelRowsAtPackage
      P)


noncomputable def OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage.toSourceSectorImageRowsAtPackage
    {β : ℝ} {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n) :
    OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAtPackage
      β n :=
  OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAtPackage.toSourceSectorImageRowsAtPackage
    (β := β)
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage.toSourceSectorImageEdgeVertexRelabelRowsAtPackage
      P)


end Exact3D
end StatMech
