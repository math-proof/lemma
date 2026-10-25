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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part116
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

def FreeQ2BoundaryVertexPolynomialAtLeastMassPositiveSubcritical : Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ (Alo AfkHi : ℕ → ℝ) (mass : ℝ),
      0 < mass →
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo AfkHi mass →
      ∃ (C boundaryMass : ℝ) (k : ℕ),
        0 < C ∧ mass ≤ boundaryMass ∧
          ∀ᶠ n in atTop,
            ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v →
              ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
                  (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
                : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                  (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
                ≤ C * (n : ℝ) ^ k *
                  Real.exp (-(boundaryMass * (n : ℝ)))


def
    FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∃ (C rate : ℝ) (k : ℕ), 0 < C ∧
      (∀ᶠ n in atTop,
        ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v →
          ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
              (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
            ≤ C * (n : ℝ) ^ k * Real.exp (-(rate * (n : ℝ)))) ∧
      Tendsto
        (fun n : ℕ =>
          -Real.log (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n) /
            (n : ℝ)) atTop (nhds rate)


def
    FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∃ (C xRate : ℝ) (k : ℕ)
      (boundaryRate : (n : ℕ) → FK.boxVerts 3 n → ℝ), 0 < C ∧
      (∀ᶠ n in atTop,
        ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v →
          xRate * (n : ℝ) ≤ boundaryRate n v) ∧
      (∀ᶠ n in atTop,
        ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v →
          ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
              (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
            : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
              (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
            ≤ C * (n : ℝ) ^ k * Real.exp (-(boundaryRate n v))) ∧
      Tendsto
        (fun n : ℕ =>
          -Real.log (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n) /
            (n : ℝ)) atTop (nhds xRate)


def surfaceVecOfBoxVertex (n : ℕ) (v : FK.boxVerts 3 n) : SurfaceVec3 :=
  surfaceVec3 (((v : Lattice.Site 3) 0 : ℝ))
    (((v : Lattice.Site 3) 1 : ℝ))
    (((v : Lattice.Site 3) 2 : ℝ))


end Exact3D
end StatMech
