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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part51
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

structure OrderedWedgePredecessorSourcePairRowsAt
    (β : ℝ) (n : ℕ) (Case : Type*) [DecidableEq Case] where
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
  soundStrictZ :
    ∀ p, rowPred (classifyStrictZ p) →
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n p.val ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n
          (boxVertStrictSectorPredecessor3 p.val p.property.1 p.property.2)
  soundDiagY :
    ∀ p, rowPred (classifyDiagY p) →
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n p.val ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n
          (boxVertDiagonalPredecessor3 p.val p.property.1 p.property.2.1
            p.property.2.2)
  soundStrictY :
    ∀ p, rowPred (classifyStrictY p) →
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n p.val ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n
          (boxVertStrictSectorYPredecessor3 p.val p.property.1
            p.property.2.1 p.property.2.2)


end Exact3D
end StatMech
