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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part66
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical_of_sourceSectorImageMultiplicityPreservingRowsPositiveSubcritical
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hrows β hβpos hβc) fun _ hn => by
    rcases hn with ⟨P⟩
    exact
      ⟨OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage.toSourceSectorImageRowsAtPackage
        (β := β) P⟩


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical_of_sourceSectorImageMultiplicityPreservingRowsPositiveSubcritical
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedCasesPositiveSubcritical_of_sourceSectorImageRowsPositiveSubcritical
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical_of_sourceSectorImageMultiplicityPreservingRowsPositiveSubcritical
      hrows)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPositiveSubcritical
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorSourcePairCasesPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical_of_sourceSectorImageMultiplicityPreservingRowsPositiveSubcritical
      hrows)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPositiveSubcritical
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical_of_sourceSectorImageMultiplicityPreservingRowsPositiveSubcritical
      hrows)

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPositiveSubcritical_of_eventually_strictZBranchPoint
    (hβexists : ∃ β : ℝ, 0 < β ∧ β < Ising.betaC 3)
    (hbranch :
      ∀ᶠ n : ℕ in Filter.atTop,
        Nonempty
          {v : FK.boxVerts 3 n //
            boxVertPositiveXFaceOrderedWedge3 n v ∧
              ((v : Lattice.Site 3) (1 : Fin 3)) <
                ((v : Lattice.Site 3) (2 : Fin 3))}) :
    ¬ FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPositiveSubcritical := by
  intro hrows
  rcases hβexists with ⟨β, hβpos, hβc⟩
  have hpkg :
      ∀ᶠ n : ℕ in Filter.atTop,
        Nonempty
          (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage
            n) :=
    hrows β hβpos hβc
  have hbad : ∀ᶠ n : ℕ in Filter.atTop, False := by
    filter_upwards [hbranch, hpkg] with n hbranch_n hpkg_n
    rcases hbranch_n with ⟨p⟩
    exact
      not_nonempty_orderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage_of_strictZ
        p hpkg_n
  rcases
      (Filter.eventually_atTop.1 hbad :
        ∃ N : ℕ, ∀ n, N ≤ n → False) with
    ⟨N, hN⟩
  exact hN N le_rfl

set_option linter.style.longLine false in


theorem
    not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPositiveSubcritical_of_exists_subcritical_beta
    (hβexists : ∃ β : ℝ, 0 < β ∧ β < Ising.betaC 3) :
    ¬ FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPositiveSubcritical :=
  not_freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPositiveSubcritical_of_eventually_strictZBranchPoint
    hβexists eventually_orderedWedgeStrictZBranchPoint_nonempty


end Exact3D
end StatMech
