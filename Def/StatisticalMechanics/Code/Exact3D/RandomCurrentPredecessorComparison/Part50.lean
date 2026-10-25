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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part52
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorEdgeCopyCollapsedComparisonAt
    (β : ℝ) (n : ℕ) :
    Prop :=
  ∀ v : FK.boxVerts 3 n,
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
      (hlt :
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3))) →
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
          doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n
            (boxVertStrictSectorPredecessor3 v hvwedge hlt)


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorEdgeCopyCollapsedComparisonAt
    (β : ℝ) (n : ℕ) :
    Prop :=
  ∀ v : FK.boxVerts 3 n,
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
      (hlt :
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3))) →
        (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
          doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
            doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorEdgeCopyCollapsedComparisonAt
    (β : ℝ) (n : ℕ) :
    Prop :=
  ∀ v : FK.boxVerts 3 n,
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
      (hheight : boxVertTransverseHeight3 v ≠ 0) →
        (hnotlt :
          ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))) →
          doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
            doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n
              (boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt)

end Exact3D
end StatMech
