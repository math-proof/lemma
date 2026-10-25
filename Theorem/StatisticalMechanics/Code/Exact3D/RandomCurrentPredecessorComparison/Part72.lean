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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part65
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical_of_sourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hrows β hβpos hβc) fun _ hn => by
    rcases hn with ⟨P⟩
    exact
      ⟨OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage.toSourceSectorImageEdgeVertexRelabelRowsAtPackage
        P⟩


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsPositiveSubcritical_of_sourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsPositiveSubcritical_of_sourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical_of_sourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical
      hrows)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical_of_sourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical_of_sourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical_of_sourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical
      hrows)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical_of_sourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical_of_sourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical_of_sourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical
      hrows)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical_of_sourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical
      hrows)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical_of_sourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical
      hrows)

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical_of_eventually_not_package
    (hβexists : ∃ β : ℝ, 0 < β ∧ β < Ising.betaC 3)
    (hnotpkg :
      ∀ᶠ n : ℕ in Filter.atTop,
        ¬ Nonempty
          (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
            n)) :
    ¬ FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical := by
  intro hrows
  rcases hβexists with ⟨β, hβpos, hβc⟩
  have hpkg :
      ∀ᶠ n : ℕ in Filter.atTop,
        Nonempty
          (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
            n) :=
    hrows β hβpos hβc
  have hbad : ∀ᶠ n : ℕ in Filter.atTop, False := by
    filter_upwards [hnotpkg, hpkg] with n hnotpkg_n hpkg_n
    exact hnotpkg_n hpkg_n
  rcases
      (Filter.eventually_atTop.1 hbad :
        ∃ N : ℕ, ∀ n, N ≤ n → False) with
    ⟨N, hN⟩
  exact hN N le_rfl

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical_of_exists_subcritical_beta
    (hβexists : ∃ β : ℝ, 0 < β ∧ β < Ising.betaC 3) :
    ¬ FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical :=
  not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical_of_eventually_not_package
    hβexists
    eventually_not_nonempty_orderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage


end Exact3D
end StatMech
