/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
public import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
public import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part66
public section

open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

structure OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage
    (n : ℕ) : Type 1 where
  Case : Type
  inst : DecidableEq Case
  table :
    @OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt
      n Case inst
  rows_sound :
    ∀ c, c ∈ table.rows → table.rowPred c


structure OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAtPackage
    (n : ℕ) : Type 1 where
  Case : Type
  inst : DecidableEq Case
  table :
    @OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAt
      n Case inst
  rows_sound :
    ∀ c, c ∈ table.rows → table.rowPred c


structure OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAtPackage
    (n : ℕ) : Type 1 where
  Case : Type
  inst : DecidableEq Case
  table :
    @OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt
      n Case inst
  rows_sound :
    ∀ c, c ∈ table.rows → table.rowPred c


structure OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
    (n : ℕ) : Type 1 where
  Case : Type
  inst : DecidableEq Case
  table :
    @OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt
      n Case inst
  rows_sound :
    ∀ c, c ∈ table.rows → table.rowPred c

end Exact3D
end StatMech
