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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part58
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

structure OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAt
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
  imageStrictZ :
    ∀ p, rowPred (classifyStrictZ p) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        EdgeCopySourceSectorImageEmbedding (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n p.val)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorPredecessor3 p.val p.property.1 p.property.2))
          m (mapStrictZ p m)
  edgeEquivStrictZ :
    ∀ p, rowPred (classifyStrictZ p) →
      ∀ _m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  multiplicityStrictZ :
    ∀ p, (hrow : rowPred (classifyStrictZ p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ e, mapStrictZ p m (edgeEquivStrictZ p hrow m e) = m e
  imageDiagY :
    ∀ p, rowPred (classifyDiagY p) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        EdgeCopySourceSectorImageEmbedding (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n p.val)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertDiagonalPredecessor3 p.val p.property.1 p.property.2.1
              p.property.2.2))
          m (mapDiagY p m)
  edgeEquivDiagY :
    ∀ p, rowPred (classifyDiagY p) →
      ∀ _m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  multiplicityDiagY :
    ∀ p, (hrow : rowPred (classifyDiagY p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ e, mapDiagY p m (edgeEquivDiagY p hrow m e) = m e
  imageStrictY :
    ∀ p, rowPred (classifyStrictY p) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        EdgeCopySourceSectorImageEmbedding (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n p.val)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 p.val p.property.1
              p.property.2.1 p.property.2.2))
          m (mapStrictY p m)
  edgeEquivStrictY :
    ∀ p, rowPred (classifyStrictY p) →
      ∀ _m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  multiplicityStrictY :
    ∀ p, (hrow : rowPred (classifyStrictY p)) →
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        ∀ e, mapStrictY p m (edgeEquivStrictY p hrow m e) = m e


end Exact3D
end StatMech
