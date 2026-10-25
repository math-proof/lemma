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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part49
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

def FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocal :
    Prop :=
  ∀ {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n},
    boxVertPositiveXFaceOrderedWedge3 n v →
      boxVertPositiveXFaceOrderedWedge3 n w →
        boxVertTransverseHeight3 w < boxVertTransverseHeight3 v →
          (FK.boxGraph 3 (2 * n)).Adj
            (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
            (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) →
          Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n v) ≤
            Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)


def FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt
    (β : ℝ) (n : ℕ) : Prop :=
  ∀ v w : FK.boxVerts 3 n,
    boxVertPositiveXFaceOrderedWedge3 n v →
      boxVertPositiveXFaceOrderedWedge3 n w →
        boxVertTransverseHeight3 w < boxVertTransverseHeight3 v →
          (FK.boxGraph 3 (2 * n)).Adj
            (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
            (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) →
          Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n v) ≤
            Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in Filter.atTop,
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt
        β n


end Exact3D
end StatMech
