/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part110
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeAdditiveStrictDescentPolynomialErrorPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ᶠ n in atTop,
        ∀ v : FK.boxVerts 3 n,
          boxVertPositiveXFaceOrderedWedge3 n v →
            boxVertTransverseHeight3 v ≠ 0 →
              ∃ w : FK.boxVerts 3 n,
                boxVertPositiveXFaceOrderedWedge3 n w ∧
                  boxVertTransverseHeight3 w < boxVertTransverseHeight3 v ∧
                    freeQ2DoubledInnerOriginConnProb β hβpos n v ≤
                      freeQ2DoubledInnerOriginConnProb β hβpos n w +
                        C * (n : ℝ) ^ k *
                          freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume
                            β hβpos (2 * n) n

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescentPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ v : FK.boxVerts 3 n,
        boxVertPositiveXFaceOrderedWedge3 n v →
          boxVertTransverseHeight3 v ≠ 0 →
            ∃ w : FK.boxVerts 3 n,
              boxVertPositiveXFaceOrderedWedge3 n w ∧
                boxVertTransverseHeight3 w < boxVertTransverseHeight3 v ∧
                  freeQ2DoubledFullOriginConnProb β hβpos n v ≤
                    freeQ2DoubledFullOriginConnProb β hβpos n w

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonAt
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) : Prop :=
  ∀ v : FK.boxVerts 3 n,
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
      (hlt :
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3))) →
        freeQ2DoubledFullOriginConnProb β hβpos n v ≤
          freeQ2DoubledFullOriginConnProb β hβpos n
            (boxVertStrictSectorPredecessor3 v hvwedge hlt)

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonAt
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) : Prop :=
  ∀ v : FK.boxVerts 3 n,
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
      (hheight : boxVertTransverseHeight3 v ≠ 0) →
        (hnotlt :
          ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))) →
          freeQ2DoubledFullOriginConnProb β hβpos n v ≤
            freeQ2DoubledFullOriginConnProb β hβpos n
              (boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt)

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonAt
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) : Prop :=
  ∀ v : FK.boxVerts 3 n,
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
      (hlt :
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3))) →
        ∃ w : FK.boxVerts 3 n,
          boxVertHasCoords3 w (n : ℤ)
            ((v : Lattice.Site 3) (1 : Fin 3))
            (((v : Lattice.Site 3) (2 : Fin 3)) - 1) ∧
            freeQ2DoubledFullOriginConnProb β hβpos n v ≤
              freeQ2DoubledFullOriginConnProb β hβpos n w

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonAt
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) : Prop :=
  ∀ v : FK.boxVerts 3 n,
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
      (hheight : boxVertTransverseHeight3 v ≠ 0) →
        (hnotlt :
          ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
            ((v : Lattice.Site 3) (2 : Fin 3))) →
          ∃ w : FK.boxVerts 3 n,
            boxVertHasCoords3 w (n : ℤ)
              (((v : Lattice.Site 3) (1 : Fin 3)) - 1)
              ((v : Lattice.Site 3) (2 : Fin 3)) ∧
              freeQ2DoubledFullOriginConnProb β hβpos n v ≤
                freeQ2DoubledFullOriginConnProb β hβpos n w

end Exact3D
end StatMech
