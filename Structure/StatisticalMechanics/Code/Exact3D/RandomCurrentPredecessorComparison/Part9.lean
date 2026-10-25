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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part55
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

structure OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAt
    (n : ℕ) (Case : Type*) [DecidableEq Case] where
  rows : Finset Case
  rowPred : Case → Prop
  classifyStrictZ :
    {v : FK.boxVerts 3 n //
      boxVertPositiveXFaceOrderedWedge3 n v ∧
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3))} → Case
  classifyDiagY :
    {v : FK.boxVerts 3 n //
      boxVertPositiveXFaceOrderedWedge3 n v ∧
        boxVertTransverseHeight3 v ≠ 0 ∧
          ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))} → Case
  classifyStrictY :
    {v : FK.boxVerts 3 n //
      boxVertPositiveXFaceOrderedWedge3 n v ∧
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3)) ∧
            0 < ((v : Lattice.Site 3) (1 : Fin 3))} → Case
  coversStrictZ :
    ∀ p, classifyStrictZ p ∈ rows
  coversDiagY :
    ∀ p, classifyDiagY p ∈ rows
  coversStrictY :
    ∀ p, classifyStrictY p ∈ rows
  mapStrictZ :
    {v : FK.boxVerts 3 n //
      boxVertPositiveXFaceOrderedWedge3 n v ∧
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3))} →
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
  mapStrictZ_injective :
    ∀ p, Function.Injective (mapStrictZ p)
  mapDiagY :
    {v : FK.boxVerts 3 n //
      boxVertPositiveXFaceOrderedWedge3 n v ∧
        boxVertTransverseHeight3 v ≠ 0 ∧
          ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))} →
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
  mapDiagY_injective :
    ∀ p, Function.Injective (mapDiagY p)
  mapStrictY :
    {v : FK.boxVerts 3 n //
      boxVertPositiveXFaceOrderedWedge3 n v ∧
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3)) ∧
            0 < ((v : Lattice.Site 3) (1 : Fin 3))} →
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
  mapStrictY_injective :
    ∀ p, Function.Injective (mapStrictY p)
  vertexEquivStrictZ :
    ∀ p, rowPred (classifyStrictZ p) →
      ∀ _m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n)
  edgeEquivStrictZ :
    ∀ p, rowPred (classifyStrictZ p) →
      ∀ _m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  multiplicityStrictZ :
    ∀ p, (hrow : rowPred (classifyStrictZ p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ e, mapStrictZ p m (edgeEquivStrictZ p hrow m e) = m e
  endsStrictZ :
    ∀ p, (hrow : rowPred (classifyStrictZ p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ e,
          (edgeEquivStrictZ p hrow m e).1 =
            Sym2.map (vertexEquivStrictZ p hrow m) e.1
  sourceStrictZ :
    ∀ p, (hrow : rowPred (classifyStrictZ p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        (doubledBoxOriginToInnerEndpointSource n p.val).map
            (vertexEquivStrictZ p hrow m).toEmbedding =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorPredecessor3 p.val p.property.1 p.property.2)
  vertexEquivDiagY :
    ∀ p, rowPred (classifyDiagY p) →
      ∀ _m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n)
  edgeEquivDiagY :
    ∀ p, rowPred (classifyDiagY p) →
      ∀ _m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  multiplicityDiagY :
    ∀ p, (hrow : rowPred (classifyDiagY p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ e, mapDiagY p m (edgeEquivDiagY p hrow m e) = m e
  endsDiagY :
    ∀ p, (hrow : rowPred (classifyDiagY p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ e,
          (edgeEquivDiagY p hrow m e).1 =
            Sym2.map (vertexEquivDiagY p hrow m) e.1
  sourceDiagY :
    ∀ p, (hrow : rowPred (classifyDiagY p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        (doubledBoxOriginToInnerEndpointSource n p.val).map
            (vertexEquivDiagY p hrow m).toEmbedding =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertDiagonalPredecessor3 p.val p.property.1 p.property.2.1
              p.property.2.2)
  vertexEquivStrictY :
    ∀ p, rowPred (classifyStrictY p) →
      ∀ _m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n)
  edgeEquivStrictY :
    ∀ p, rowPred (classifyStrictY p) →
      ∀ _m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  multiplicityStrictY :
    ∀ p, (hrow : rowPred (classifyStrictY p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ e, mapStrictY p m (edgeEquivStrictY p hrow m e) = m e
  endsStrictY :
    ∀ p, (hrow : rowPred (classifyStrictY p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ e,
          (edgeEquivStrictY p hrow m e).1 =
            Sym2.map (vertexEquivStrictY p hrow m) e.1
  sourceStrictY :
    ∀ p, (hrow : rowPred (classifyStrictY p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        (doubledBoxOriginToInnerEndpointSource n p.val).map
            (vertexEquivStrictY p hrow m).toEmbedding =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 p.val p.property.1
              p.property.2.1 p.property.2.2)

set_option linter.style.longLine false in


structure OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt
    (n : ℕ) (Case : Type*) [DecidableEq Case] where
  rows : Finset Case
  rowPred : Case → Prop
  classifyStrictZ :
    {v : FK.boxVerts 3 n //
      boxVertPositiveXFaceOrderedWedge3 n v ∧
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3))} → Case
  classifyDiagY :
    {v : FK.boxVerts 3 n //
      boxVertPositiveXFaceOrderedWedge3 n v ∧
        boxVertTransverseHeight3 v ≠ 0 ∧
          ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))} → Case
  classifyStrictY :
    {v : FK.boxVerts 3 n //
      boxVertPositiveXFaceOrderedWedge3 n v ∧
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3)) ∧
            0 < ((v : Lattice.Site 3) (1 : Fin 3))} → Case
  coversStrictZ :
    ∀ p, classifyStrictZ p ∈ rows
  coversDiagY :
    ∀ p, classifyDiagY p ∈ rows
  coversStrictY :
    ∀ p, classifyStrictY p ∈ rows
  mapStrictZ :
    {v : FK.boxVerts 3 n //
      boxVertPositiveXFaceOrderedWedge3 n v ∧
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3))} →
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
  mapStrictZ_injective :
    ∀ p, Function.Injective (mapStrictZ p)
  mapDiagY :
    {v : FK.boxVerts 3 n //
      boxVertPositiveXFaceOrderedWedge3 n v ∧
        boxVertTransverseHeight3 v ≠ 0 ∧
          ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))} →
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
  mapDiagY_injective :
    ∀ p, Function.Injective (mapDiagY p)
  mapStrictY :
    {v : FK.boxVerts 3 n //
      boxVertPositiveXFaceOrderedWedge3 n v ∧
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3)) ∧
            0 < ((v : Lattice.Site 3) (1 : Fin 3))} →
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
  mapStrictY_injective :
    ∀ p, Function.Injective (mapStrictY p)
  vertexEquivStrictZ :
    ∀ p, rowPred (classifyStrictZ p) →
      ∀ _m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n)
  edgeEquivStrictZ :
    ∀ p, rowPred (classifyStrictZ p) →
      ∀ _m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  multiplicityStrictZ :
    ∀ p, (hrow : rowPred (classifyStrictZ p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ e, mapStrictZ p m (edgeEquivStrictZ p hrow m e) = m e
  endsStrictZ :
    ∀ p, (hrow : rowPred (classifyStrictZ p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ e,
          (edgeEquivStrictZ p hrow m e).1 =
            Sym2.map (vertexEquivStrictZ p hrow m) e.1
  originStrictZ :
    ∀ p, (hrow : rowPred (classifyStrictZ p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        vertexEquivStrictZ p hrow m (IsingFK.boxOrigin 3 (2 * n)) =
          IsingFK.boxOrigin 3 (2 * n)
  endpointStrictZ :
    ∀ p, (hrow : rowPred (classifyStrictZ p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        vertexEquivStrictZ p hrow m
            (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) =
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorPredecessor3 p.val p.property.1 p.property.2)
  vertexEquivDiagY :
    ∀ p, rowPred (classifyDiagY p) →
      ∀ _m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n)
  edgeEquivDiagY :
    ∀ p, rowPred (classifyDiagY p) →
      ∀ _m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  multiplicityDiagY :
    ∀ p, (hrow : rowPred (classifyDiagY p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ e, mapDiagY p m (edgeEquivDiagY p hrow m e) = m e
  endsDiagY :
    ∀ p, (hrow : rowPred (classifyDiagY p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ e,
          (edgeEquivDiagY p hrow m e).1 =
            Sym2.map (vertexEquivDiagY p hrow m) e.1
  originDiagY :
    ∀ p, (hrow : rowPred (classifyDiagY p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        vertexEquivDiagY p hrow m (IsingFK.boxOrigin 3 (2 * n)) =
          IsingFK.boxOrigin 3 (2 * n)
  endpointDiagY :
    ∀ p, (hrow : rowPred (classifyDiagY p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        vertexEquivDiagY p hrow m
            (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) =
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertDiagonalPredecessor3 p.val p.property.1 p.property.2.1
              p.property.2.2)
  vertexEquivStrictY :
    ∀ p, rowPred (classifyStrictY p) →
      ∀ _m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n)
  edgeEquivStrictY :
    ∀ p, rowPred (classifyStrictY p) →
      ∀ _m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  multiplicityStrictY :
    ∀ p, (hrow : rowPred (classifyStrictY p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ e, mapStrictY p m (edgeEquivStrictY p hrow m e) = m e
  endsStrictY :
    ∀ p, (hrow : rowPred (classifyStrictY p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ e,
          (edgeEquivStrictY p hrow m e).1 =
            Sym2.map (vertexEquivStrictY p hrow m) e.1
  originStrictY :
    ∀ p, (hrow : rowPred (classifyStrictY p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        vertexEquivStrictY p hrow m (IsingFK.boxOrigin 3 (2 * n)) =
          IsingFK.boxOrigin 3 (2 * n)
  endpointStrictY :
    ∀ p, (hrow : rowPred (classifyStrictY p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        vertexEquivStrictY p hrow m
            (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) =
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 p.val p.property.1
              p.property.2.1 p.property.2.2)

end Exact3D
end StatMech
