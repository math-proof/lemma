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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part54
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt.not_rowPred_strictZ
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))}) :
    ¬ T.rowPred (T.classifyStrictZ p) := by
  intro hrow
  let w := boxVertStrictSectorPredecessor3 p.val p.property.1 p.property.2
  have hwwedge : boxVertPositiveXFaceOrderedWedge3 n w :=
    boxVertStrictSectorPredecessor3_wedge p.val p.property.1 p.property.2
  have hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 p.val :=
    boxVertStrictSectorPredecessor3_height_lt p.val p.property.1 p.property.2
  have hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) :=
    boxGraph_adj_boxVertInclLE_strictSectorPredecessor3
      (by omega : n ≤ 2 * n) p.val p.property.1 p.property.2
  have hsource_ne :
      doubledBoxOriginToInnerEndpointSource n p.val ≠
        doubledBoxOriginToInnerEndpointSource n w :=
    doubledBoxOriginToInnerEndpointSource_ne_of_orderedWedge_lowerDoubledAdj
      p.property.1 hwwedge hheight hadj
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        p.property.1 hwwedge hheight hadj with
    ⟨_e0, _hedge, hov, _how, _hvw⟩
  rcases
      boxGraph_reachable 3 (2 * n) (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) with
    ⟨walk⟩
  let G := FK.boxGraph 3 (2 * n)
  let m : ↥G.edgeFinset → ℕ := fun e => walk.edges.count e.1
  have hsrc0 :
      Sharpness.sources G (Sharpness.ofEdgeFun G m) =
        ({IsingFK.boxOrigin 3 (2 * n),
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val} :
          Finset (FK.boxVerts 3 (2 * n))) := by
    simpa [G, m] using sources_ofEdgeFun_walk_count G walk hov
  have hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) =
          doubledBoxOriginToInnerEndpointSource n p.val := by
    rw [Sharpness.FluxEdgeCopy.sources_eq,
      Sharpness.FluxEdgeCopy.profileFlux_univ]
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair hov]
    simpa [G, m] using hsrc0
  exact hsource_ne
    ((T.imageStrictZ p hrow m).source_eq_of_edge_multiplicity_eq
      (T.multiplicityStrictZ p hrow m) hfull)

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt.not_rowPred_diagY
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          boxVertTransverseHeight3 v ≠ 0 ∧
            ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))}) :
    ¬ T.rowPred (T.classifyDiagY p) := by
  intro hrow
  let w :=
    boxVertDiagonalPredecessor3 p.val p.property.1 p.property.2.1
      p.property.2.2
  have hwwedge : boxVertPositiveXFaceOrderedWedge3 n w :=
    boxVertDiagonalPredecessor3_wedge p.val p.property.1 p.property.2.1
      p.property.2.2
  have hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 p.val :=
    boxVertDiagonalPredecessor3_height_lt p.val p.property.1 p.property.2.1
      p.property.2.2
  have hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) :=
    boxGraph_adj_boxVertInclLE_diagonalPredecessor3
      (by omega : n ≤ 2 * n) p.val p.property.1 p.property.2.1
      p.property.2.2
  have hsource_ne :
      doubledBoxOriginToInnerEndpointSource n p.val ≠
        doubledBoxOriginToInnerEndpointSource n w :=
    doubledBoxOriginToInnerEndpointSource_ne_of_orderedWedge_lowerDoubledAdj
      p.property.1 hwwedge hheight hadj
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        p.property.1 hwwedge hheight hadj with
    ⟨_e0, _hedge, hov, _how, _hvw⟩
  rcases
      boxGraph_reachable 3 (2 * n) (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) with
    ⟨walk⟩
  let G := FK.boxGraph 3 (2 * n)
  let m : ↥G.edgeFinset → ℕ := fun e => walk.edges.count e.1
  have hsrc0 :
      Sharpness.sources G (Sharpness.ofEdgeFun G m) =
        ({IsingFK.boxOrigin 3 (2 * n),
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val} :
          Finset (FK.boxVerts 3 (2 * n))) := by
    simpa [G, m] using sources_ofEdgeFun_walk_count G walk hov
  have hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) =
          doubledBoxOriginToInnerEndpointSource n p.val := by
    rw [Sharpness.FluxEdgeCopy.sources_eq,
      Sharpness.FluxEdgeCopy.profileFlux_univ]
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair hov]
    simpa [G, m] using hsrc0
  exact hsource_ne
    ((T.imageDiagY p hrow m).source_eq_of_edge_multiplicity_eq
      (T.multiplicityDiagY p hrow m) hfull)

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt.not_rowPred_strictY
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((v : Lattice.Site 3) (1 : Fin 3))}) :
    ¬ T.rowPred (T.classifyStrictY p) := by
  intro hrow
  let w :=
    boxVertStrictSectorYPredecessor3 p.val p.property.1 p.property.2.1
      p.property.2.2
  have hwwedge : boxVertPositiveXFaceOrderedWedge3 n w :=
    boxVertStrictSectorYPredecessor3_wedge p.val p.property.1
      p.property.2.1 p.property.2.2
  have hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 p.val :=
    boxVertStrictSectorYPredecessor3_height_lt p.val p.property.1
      p.property.2.1 p.property.2.2
  have hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) :=
    boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
      (by omega : n ≤ 2 * n) p.val p.property.1 p.property.2.1
      p.property.2.2
  have hsource_ne :
      doubledBoxOriginToInnerEndpointSource n p.val ≠
        doubledBoxOriginToInnerEndpointSource n w :=
    doubledBoxOriginToInnerEndpointSource_ne_of_orderedWedge_lowerDoubledAdj
      p.property.1 hwwedge hheight hadj
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        p.property.1 hwwedge hheight hadj with
    ⟨_e0, _hedge, hov, _how, _hvw⟩
  rcases
      boxGraph_reachable 3 (2 * n) (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) with
    ⟨walk⟩
  let G := FK.boxGraph 3 (2 * n)
  let m : ↥G.edgeFinset → ℕ := fun e => walk.edges.count e.1
  have hsrc0 :
      Sharpness.sources G (Sharpness.ofEdgeFun G m) =
        ({IsingFK.boxOrigin 3 (2 * n),
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val} :
          Finset (FK.boxVerts 3 (2 * n))) := by
    simpa [G, m] using sources_ofEdgeFun_walk_count G walk hov
  have hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) =
          doubledBoxOriginToInnerEndpointSource n p.val := by
    rw [Sharpness.FluxEdgeCopy.sources_eq,
      Sharpness.FluxEdgeCopy.profileFlux_univ]
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair hov]
    simpa [G, m] using hsrc0
  exact hsource_ne
    ((T.imageStrictY p hrow m).source_eq_of_edge_multiplicity_eq
      (T.multiplicityStrictY p hrow m) hfull)

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt.not_rows_sound_of_strictZ
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))}) :
    ¬ ∀ c, c ∈ T.rows → T.rowPred c := by
  intro hrows
  exact T.not_rowPred_strictZ p
    (hrows (T.classifyStrictZ p) (T.coversStrictZ p))

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt.not_rows_sound_of_diagY
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          boxVertTransverseHeight3 v ≠ 0 ∧
            ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))}) :
    ¬ ∀ c, c ∈ T.rows → T.rowPred c := by
  intro hrows
  exact T.not_rowPred_diagY p
    (hrows (T.classifyDiagY p) (T.coversDiagY p))

set_option linter.style.longLine false in


theorem OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt.not_rows_sound_of_strictY
    {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAt
        n Case)
    (p :
      {v : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n v ∧
          ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((v : Lattice.Site 3) (1 : Fin 3))}) :
    ¬ ∀ c, c ∈ T.rows → T.rowPred c := by
  intro hrows
  exact T.not_rowPred_strictY p
    (hrows (T.classifyStrictY p) (T.coversStrictY p))


end Exact3D
end StatMech
