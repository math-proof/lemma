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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part67
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

structure OrderedWedgePredecessorExpectationJRowsAt
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
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n p.val) ≤
        Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorPredecessor3 p.val p.property.1 p.property.2))
  soundDiagY :
    ∀ p, rowPred (classifyDiagY p) →
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n p.val) ≤
        Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertDiagonalPredecessor3 p.val p.property.1 p.property.2.1
              p.property.2.2))
  soundStrictY :
    ∀ p, rowPred (classifyStrictY p) →
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n p.val) ≤
        Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 p.val p.property.1
              p.property.2.1 p.property.2.2))

set_option linter.style.longLine false in


structure OrderedWedgeStrictSectorYPredecessorExpectationJRowsAt
    (β : ℝ) (n : ℕ) (Case : Type*) [DecidableEq Case] where
  rows : Finset Case
  rowPred : Case → Prop
  classify :
    {v : FK.boxVerts 3 n //
      boxVertPositiveXFaceOrderedWedge3 n v ∧
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3)) ∧
            0 < ((v : Lattice.Site 3) (1 : Fin 3))} → Case
  covers :
    ∀ p, classify p ∈ rows
  sound :
    ∀ p, rowPred (classify p) →
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n p.val) ≤
        Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 p.val p.property.1
              p.property.2.1 p.property.2.2))


end Exact3D
end StatMech
