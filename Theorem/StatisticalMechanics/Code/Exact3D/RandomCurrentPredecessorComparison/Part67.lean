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
import Structure.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part12
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage.false_of_strictZ
    {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage
        n)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))}) :
    False := by
  letI := P.inst
  exact (P.table.not_rows_sound_of_strictZ p) P.rows_sound

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage.false_of_diagY
    {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage
        n)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          boxVertTransverseHeight3 v ≠ 0 ∧
            ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))}) :
    False := by
  letI := P.inst
  exact (P.table.not_rows_sound_of_diagY p) P.rows_sound

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage.false_of_strictY
    {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage
        n)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((v : Lattice.Site 3) (1 : Fin 3))}) :
    False := by
  letI := P.inst
  exact (P.table.not_rows_sound_of_strictY p) P.rows_sound

set_option linter.style.longLine false in


theorem not_nonempty_orderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage_of_strictZ
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))}) :
    ¬ Nonempty
      (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage
        n) := by
  rintro ⟨P⟩
  exact P.false_of_strictZ p

set_option linter.style.longLine false in


theorem not_nonempty_orderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage_of_diagY
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          boxVertTransverseHeight3 v ≠ 0 ∧
            ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))}) :
    ¬ Nonempty
      (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage
        n) := by
  rintro ⟨P⟩
  exact P.false_of_diagY p

set_option linter.style.longLine false in


theorem not_nonempty_orderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage_of_strictY
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((v : Lattice.Site 3) (1 : Fin 3))}) :
    ¬ Nonempty
      (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage
        n) := by
  rintro ⟨P⟩
  exact P.false_of_strictY p

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage.false_of_strictZ_endpointMapObstruction
    {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))})
    (hobs :
      doubledBoxEndpointMapObstruction n p.val
        (boxVertStrictSectorPredecessor3 p.val p.property.1 p.property.2)) :
    False := by
  letI := P.inst
  exact
    (P.table.not_rowPred_strictZ_of_endpointMapObstruction p hobs)
      (P.rows_sound (P.table.classifyStrictZ p) (P.table.coversStrictZ p))

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage.false_of_diagY_endpointMapObstruction
    {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          boxVertTransverseHeight3 v ≠ 0 ∧
            ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))})
    (hobs :
      doubledBoxEndpointMapObstruction n p.val
        (boxVertDiagonalPredecessor3 p.val p.property.1 p.property.2.1
          p.property.2.2)) :
    False := by
  letI := P.inst
  exact
    (P.table.not_rowPred_diagY_of_endpointMapObstruction p hobs)
      (P.rows_sound (P.table.classifyDiagY p) (P.table.coversDiagY p))

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage.false_of_strictY_endpointMapObstruction
    {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((v : Lattice.Site 3) (1 : Fin 3))})
    (hobs :
      doubledBoxEndpointMapObstruction n p.val
        (boxVertStrictSectorYPredecessor3 p.val p.property.1
          p.property.2.1 p.property.2.2)) :
    False := by
  letI := P.inst
  exact
    (P.table.not_rowPred_strictY_of_endpointMapObstruction p hobs)
      (P.rows_sound (P.table.classifyStrictY p) (P.table.coversStrictY p))

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage.false_of_strictZ_origin_edist_ne
    {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))})
    (hdist :
      (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) ≠
        (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorPredecessor3 p.val p.property.1
              p.property.2))) :
    False := by
  exact
    P.false_of_strictZ_endpointMapObstruction p
      (doubledBoxEndpointMapObstruction_strictZ_of_origin_edist_ne p hdist)

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage.false_of_diagY_origin_edist_ne
    {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          boxVertTransverseHeight3 v ≠ 0 ∧
            ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))})
    (hdist :
      (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) ≠
        (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertDiagonalPredecessor3 p.val p.property.1
              p.property.2.1 p.property.2.2))) :
    False := by
  exact
    P.false_of_diagY_endpointMapObstruction p
      (doubledBoxEndpointMapObstruction_diagY_of_origin_edist_ne p hdist)

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage.false_of_strictY_origin_edist_ne
    {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((v : Lattice.Site 3) (1 : Fin 3))})
    (hdist :
      (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) ≠
        (FK.boxGraph 3 (2 * n)).edist
          (IsingFK.boxOrigin 3 (2 * n))
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 p.val p.property.1
              p.property.2.1 p.property.2.2))) :
    False := by
  exact
    P.false_of_strictY_endpointMapObstruction p
      (doubledBoxEndpointMapObstruction_strictY_of_origin_edist_ne p hdist)

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage.false_of_strictZ
    {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))}) :
    False :=
  P.false_of_strictZ_endpointMapObstruction p
    (doubledBoxEndpointMapObstruction_strictZ p)

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage.false_of_diagY
    {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          boxVertTransverseHeight3 v ≠ 0 ∧
            ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))}) :
    False :=
  P.false_of_diagY_endpointMapObstruction p
    (doubledBoxEndpointMapObstruction_diagY p)

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage.false_of_strictY
    {n : ℕ}
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((v : Lattice.Site 3) (1 : Fin 3))}) :
    False :=
  P.false_of_strictY_endpointMapObstruction p
    (doubledBoxEndpointMapObstruction_strictY p)

set_option linter.style.longLine false in


theorem not_nonempty_orderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage_of_strictZ
    {n : ℕ}
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))}) :
    ¬ Nonempty
      (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n) := by
  rintro ⟨P⟩
  exact P.false_of_strictZ p

set_option linter.style.longLine false in


theorem orderedWedgeStrictZBranchPoint_nonempty_of_pos
    {n : ℕ} (hn : 0 < n) :
    Nonempty
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))} := by
  let v : FK.boxVerts 3 n :=
    boxVertOfCoords3 n (n : ℤ) 0 1 (by simp) (by simp) (by omega)
  have hv : boxVertHasCoords3 v (n : ℤ) 0 1 := by
    simp [v]
  have hy : ((v : Lattice.Site 3) (1 : Fin 3)) = 0 := hv.2.1
  have hz : ((v : Lattice.Site 3) (2 : Fin 3)) = 1 := hv.2.2
  refine ⟨⟨v, ?_⟩⟩
  constructor
  · refine ⟨hv.1, ?_, ?_⟩
    · simp [hy]
    · simp [hy, hz]
  · simp [hy, hz]

set_option linter.style.longLine false in


theorem not_nonempty_orderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage_of_pos
    {n : ℕ} (hn : 0 < n) :
    ¬ Nonempty
      (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n) := by
  rcases orderedWedgeStrictZBranchPoint_nonempty_of_pos hn with ⟨p⟩
  exact
    not_nonempty_orderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage_of_strictZ
      p

set_option linter.style.longLine false in

theorem eventually_orderedWedgeStrictZBranchPoint_nonempty :
    ∀ᶠ n : ℕ in Filter.atTop,
      Nonempty
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))} := by
  exact Filter.eventually_atTop.2
    ⟨1, fun n hn => orderedWedgeStrictZBranchPoint_nonempty_of_pos (by omega)⟩

set_option linter.style.longLine false in


theorem eventually_not_nonempty_orderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage :
    ∀ᶠ n : ℕ in Filter.atTop,
      ¬ Nonempty
        (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
          n) := by
  exact Filter.eventually_atTop.2
    ⟨1, fun n hn =>
      not_nonempty_orderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage_of_pos
        (by omega)⟩


end Exact3D
end StatMech
