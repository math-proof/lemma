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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part108
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ v : FK.boxVerts 3 n,
        boxVertPositiveXFaceOrderedWedge3 n v →
          ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
              (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
            ≤ freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos
                (2 * n) n


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictDescentDoubledBoxProjectionPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ v : FK.boxVerts 3 n,
        boxVertPositiveXFaceOrderedWedge3 n v →
          boxVertTransverseHeight3 v ≠ 0 →
            ∃ w : FK.boxVerts 3 n,
              boxVertPositiveXFaceOrderedWedge3 n w ∧
                boxVertTransverseHeight3 w < boxVertTransverseHeight3 v ∧
                  ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
                      (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
                    : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                      (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
                    ≤
                  ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
                      (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
                    : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                      (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) w)


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ v : FK.boxVerts 3 n,
        boxVertPositiveXFaceOrderedWedge3 n v →
          boxVertTransverseHeight3 v ≠ 0 →
            let y : ℤ := (v : Lattice.Site 3) (1 : Fin 3)
            let z : ℤ := (v : Lattice.Site 3) (2 : Fin 3)
            if y < z then
              ∃ w : FK.boxVerts 3 n,
                boxVertHasCoords3 w (n : ℤ) y (z - 1) ∧
                  ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
                      (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
                    : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                      (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
                    ≤
                  ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
                      (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
                    : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                      (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) w)
            else
              ∃ w : FK.boxVerts 3 n,
                boxVertHasCoords3 w (n : ℤ) (y - 1) z ∧
                  ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
                      (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
                    : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                      (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
                    ≤
                  ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos)
                      (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
                    : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                      (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) w)


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepAt
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) : Prop :=
  ∀ v : FK.boxVerts 3 n,
    boxVertPositiveXFaceOrderedWedge3 n v →
      let y : ℤ := (v : Lattice.Site 3) (1 : Fin 3)
      let z : ℤ := (v : Lattice.Site 3) (2 : Fin 3)
      y < z →
        ∃ w : FK.boxVerts 3 n,
          boxVertHasCoords3 w (n : ℤ) y (z - 1) ∧
            freeQ2DoubledInnerOriginConnProb β hβpos n v ≤
              freeQ2DoubledInnerOriginConnProb β hβpos n w


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepAt
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) : Prop :=
  ∀ v : FK.boxVerts 3 n,
    boxVertPositiveXFaceOrderedWedge3 n v →
      boxVertTransverseHeight3 v ≠ 0 →
        let y : ℤ := (v : Lattice.Site 3) (1 : Fin 3)
        let z : ℤ := (v : Lattice.Site 3) (2 : Fin 3)
        ¬ y < z →
          ∃ w : FK.boxVerts 3 n,
            boxVertHasCoords3 w (n : ℤ) (y - 1) z ∧
              freeQ2DoubledInnerOriginConnProb β hβpos n v ≤
                freeQ2DoubledInnerOriginConnProb β hβpos n w


def FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepAt
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepAt
      β hβpos n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepAt
      β hβpos n


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepAt
        β hβpos n


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepAt
        β hβpos n


end Exact3D
end StatMech
