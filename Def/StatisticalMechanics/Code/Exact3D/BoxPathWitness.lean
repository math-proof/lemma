/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness
open Filter


namespace StatMech

namespace Exact3D

open StatMech.Lattice


set_option linter.style.longLine false in


def FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentAt
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) : Prop :=
  ∀ v w : FK.boxVerts 3 n,
    boxVertPositiveXFaceOrderedWedge3 n v →
      boxVertPositiveXFaceOrderedWedge3 n w →
        boxVertTransverseHeight3 w < boxVertTransverseHeight3 v →
          (FK.boxGraph 3 (2 * n)).Adj
            (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
            (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) →
          freeQ2DoubledFullOriginConnProb β hβpos n v ≤
            freeQ2DoubledFullOriginConnProb β hβpos n w

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentAt
        β hβpos n

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal :
    Prop :=
  ∀ {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n},
    boxVertPositiveXFaceOrderedWedge3 n v →
      boxVertPositiveXFaceOrderedWedge3 n w →
        boxVertTransverseHeight3 w < boxVertTransverseHeight3 v →
          (FK.boxGraph 3 (2 * n)).Adj
            (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
            (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) →
          freeQ2DoubledFullOriginConnProb β hβpos n v ≤
            freeQ2DoubledFullOriginConnProb β hβpos n w

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonLocal :
    Prop :=
  ∀ {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n},
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
      (hlt :
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3))) →
        0 < ((v : Lattice.Site 3) (1 : Fin 3)) →
        boxVertHasCoords3 w (n : ℤ)
          (((v : Lattice.Site 3) (1 : Fin 3)) - 1)
          ((v : Lattice.Site 3) (2 : Fin 3)) →
          freeQ2DoubledFullOriginConnProb β hβpos n v ≤
            freeQ2DoubledFullOriginConnProb β hβpos n w

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonAt
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) : Prop :=
  ∀ v w : FK.boxVerts 3 n,
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
      (hlt :
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3))) →
        0 < ((v : Lattice.Site 3) (1 : Fin 3)) →
        boxVertHasCoords3 w (n : ℤ)
          (((v : Lattice.Site 3) (1 : Fin 3)) - 1)
          ((v : Lattice.Site 3) (2 : Fin 3)) →
          freeQ2DoubledFullOriginConnProb β hβpos n v ≤
            freeQ2DoubledFullOriginConnProb β hβpos n w

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonAt
        β hβpos n

end Exact3D
end StatMech
