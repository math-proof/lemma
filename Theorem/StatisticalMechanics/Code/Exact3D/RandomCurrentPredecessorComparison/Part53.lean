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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part50
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorEdgeCopyCollapsedComparisonAt_of_reindex_edgeEquivVertexEquiv
    {β : ℝ} {n : ℕ} (hβ : 0 ≤ β)
    (f :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))}) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hf : ∀ p, Function.Injective (f p))
    (φ :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))}) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n))
    (σ :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))}) →
        (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
            ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hm : ∀ p m e, f p m (σ p m e) = m e)
    (hends : ∀ p m e, (σ p m e).1 = Sym2.map (φ p m) e.1)
    (hsrc :
      ∀ p m,
        (doubledBoxOriginToInnerEndpointSource n p.val).map
            (φ p m).toEmbedding =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorPredecessor3 p.val p.property.1 p.property.2)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorEdgeCopyCollapsedComparisonAt
      β n := by
  intro v hvwedge hlt
  let p :
      {u : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n u ∧
          ((u : Lattice.Site 3) (1 : Fin 3)) <
            ((u : Lattice.Site 3) (2 : Fin 3))} :=
    ⟨v, hvwedge, hlt⟩
  exact
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_reindex_edgeEquivVertexEquiv
      hβ (f p) (hf p) (φ p) (σ p) (hm p) (hends p) (hsrc p)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorEdgeCopyCollapsedComparisonAt_of_reindex_edgeEquivVertexEquiv
    {β : ℝ} {n : ℕ} (hβ : 0 ≤ β)
    (f :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            boxVertTransverseHeight3 v ≠ 0 ∧
              ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
                ((v : Lattice.Site 3) (2 : Fin 3))}) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hf : ∀ p, Function.Injective (f p))
    (φ :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            boxVertTransverseHeight3 v ≠ 0 ∧
              ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
                ((v : Lattice.Site 3) (2 : Fin 3))}) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n))
    (σ :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            boxVertTransverseHeight3 v ≠ 0 ∧
              ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
                ((v : Lattice.Site 3) (2 : Fin 3))}) →
        (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
            ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hm : ∀ p m e, f p m (σ p m e) = m e)
    (hends : ∀ p m e, (σ p m e).1 = Sym2.map (φ p m) e.1)
    (hsrc :
      ∀ p m,
        (doubledBoxOriginToInnerEndpointSource n p.val).map
            (φ p m).toEmbedding =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertDiagonalPredecessor3 p.val p.property.1 p.property.2.1
              p.property.2.2)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorEdgeCopyCollapsedComparisonAt
      β n := by
  intro v hvwedge hheight hnotlt
  let p :
      {u : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n u ∧
          boxVertTransverseHeight3 u ≠ 0 ∧
            ¬ ((u : Lattice.Site 3) (1 : Fin 3)) <
              ((u : Lattice.Site 3) (2 : Fin 3))} :=
    ⟨v, hvwedge, hheight, hnotlt⟩
  exact
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_reindex_edgeEquivVertexEquiv
      hβ (f p) (hf p) (φ p) (σ p) (hm p) (hends p) (hsrc p)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorEdgeCopyCollapsedComparisonAt_of_reindex_edgeEquivVertexEquiv
    {β : ℝ} {n : ℕ} (hβ : 0 ≤ β)
    (f :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3)) ∧
                0 < ((v : Lattice.Site 3) (1 : Fin 3))}) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hf : ∀ p, Function.Injective (f p))
    (φ :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3)) ∧
                0 < ((v : Lattice.Site 3) (1 : Fin 3))}) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n))
    (σ :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3)) ∧
                0 < ((v : Lattice.Site 3) (1 : Fin 3))}) →
        (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
            ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hm : ∀ p m e, f p m (σ p m e) = m e)
    (hends : ∀ p m e, (σ p m e).1 = Sym2.map (φ p m) e.1)
    (hsrc :
      ∀ p m,
        (doubledBoxOriginToInnerEndpointSource n p.val).map
            (φ p m).toEmbedding =
          doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 p.val p.property.1
              p.property.2.1 p.property.2.2)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorEdgeCopyCollapsedComparisonAt
      β n := by
  intro v hvwedge hlt hypos
  let p :
      {u : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n u ∧
          ((u : Lattice.Site 3) (1 : Fin 3)) <
            ((u : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((u : Lattice.Site 3) (1 : Fin 3))} :=
    ⟨v, hvwedge, hlt, hypos⟩
  exact
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_reindex_edgeEquivVertexEquiv
      hβ (f p) (hf p) (φ p) (σ p) (hm p) (hends p) (hsrc p)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorEdgeCopyCollapsedComparisonAt_of_reindex_edgeEquivVertexEquiv_maps_origin_endpoint
    {β : ℝ} {n : ℕ} (hβ : 0 ≤ β)
    (f :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))}) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hf : ∀ p, Function.Injective (f p))
    (φ :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))}) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n))
    (σ :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))}) →
        (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
            ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hm : ∀ p m e, f p m (σ p m e) = m e)
    (hends : ∀ p m e, (σ p m e).1 = Sym2.map (φ p m) e.1)
    (horigin :
      ∀ p m, φ p m (IsingFK.boxOrigin 3 (2 * n)) =
        IsingFK.boxOrigin 3 (2 * n))
    (hend :
      ∀ p m,
        φ p m (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) =
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorPredecessor3 p.val p.property.1 p.property.2)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorEdgeCopyCollapsedComparisonAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorEdgeCopyCollapsedComparisonAt_of_reindex_edgeEquivVertexEquiv
    hβ f hf φ σ hm hends
    (fun p m =>
      doubledBoxOriginToInnerEndpointSource_map_eq_strictSectorPredecessor_of_maps_origin_endpoint
        p (φ p m) (horigin p m) (hend p m))

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorEdgeCopyCollapsedComparisonAt_of_reindex_edgeEquivVertexEquiv_maps_origin_endpoint
    {β : ℝ} {n : ℕ} (hβ : 0 ≤ β)
    (f :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            boxVertTransverseHeight3 v ≠ 0 ∧
              ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
                ((v : Lattice.Site 3) (2 : Fin 3))}) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hf : ∀ p, Function.Injective (f p))
    (φ :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            boxVertTransverseHeight3 v ≠ 0 ∧
              ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
                ((v : Lattice.Site 3) (2 : Fin 3))}) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n))
    (σ :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            boxVertTransverseHeight3 v ≠ 0 ∧
              ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
                ((v : Lattice.Site 3) (2 : Fin 3))}) →
        (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
            ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hm : ∀ p m e, f p m (σ p m e) = m e)
    (hends : ∀ p m e, (σ p m e).1 = Sym2.map (φ p m) e.1)
    (horigin :
      ∀ p m, φ p m (IsingFK.boxOrigin 3 (2 * n)) =
        IsingFK.boxOrigin 3 (2 * n))
    (hend :
      ∀ p m,
        φ p m (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) =
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertDiagonalPredecessor3 p.val p.property.1 p.property.2.1
              p.property.2.2)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorEdgeCopyCollapsedComparisonAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorEdgeCopyCollapsedComparisonAt_of_reindex_edgeEquivVertexEquiv
    hβ f hf φ σ hm hends
    (fun p m =>
      doubledBoxOriginToInnerEndpointSource_map_eq_diagonalPredecessor_of_maps_origin_endpoint
        p (φ p m) (horigin p m) (hend p m))

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorEdgeCopyCollapsedComparisonAt_of_reindex_edgeEquivVertexEquiv_maps_origin_endpoint
    {β : ℝ} {n : ℕ} (hβ : 0 ≤ β)
    (f :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3)) ∧
                0 < ((v : Lattice.Site 3) (1 : Fin 3))}) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hf : ∀ p, Function.Injective (f p))
    (φ :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3)) ∧
                0 < ((v : Lattice.Site 3) (1 : Fin 3))}) →
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n))
    (σ :
      (p :
        {v : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n v ∧
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3)) ∧
                0 < ((v : Lattice.Site 3) (1 : Fin 3))}) →
        (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
          ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
            ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hm : ∀ p m e, f p m (σ p m e) = m e)
    (hends : ∀ p m e, (σ p m e).1 = Sym2.map (φ p m) e.1)
    (horigin :
      ∀ p m, φ p m (IsingFK.boxOrigin 3 (2 * n)) =
        IsingFK.boxOrigin 3 (2 * n))
    (hend :
      ∀ p m,
        φ p m (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) p.val) =
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 p.val p.property.1
              p.property.2.1 p.property.2.2)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorEdgeCopyCollapsedComparisonAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorEdgeCopyCollapsedComparisonAt_of_reindex_edgeEquivVertexEquiv
    hβ f hf φ σ hm hends
    (fun p m =>
      doubledBoxOriginToInnerEndpointSource_map_eq_strictSectorYPredecessor_of_maps_origin_endpoint
        p (φ p m) (horigin p m) (hend p m))


end Exact3D
end StatMech
