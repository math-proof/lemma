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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part9
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

def
    FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ (Alo AfkHi : ℕ → ℝ) (mass : ℝ),
      0 < mass →
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo AfkHi mass →
      ∃ Apoint : ℕ → ℝ,
        PositiveSubexponentialPrefactor Apoint ∧
          ∀ᶠ n in atTop,
            ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v →
              ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
                  (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
                : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
                  (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
                ≤ Apoint n * Real.exp (-(mass * (n : ℝ)))


def FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∃ Aratio : ℕ → ℝ,
      PositiveSubexponentialPrefactor Aratio ∧
        ∀ᶠ n in atTop,
          freeQ2BoundaryProfileOfBeta β hβpos n ≤
            Aratio n *
              freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n


def
    FreeQ2BoundaryProfilePolynomialComparisonToXAxisPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ᶠ n in atTop,
        freeQ2BoundaryProfileOfBeta β hβpos n ≤
          C * (n : ℝ) ^ k *
            freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n


def
    FreeQ2BoundaryProfileFiniteVolumeComparisonToXAxisPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∃ Aratio : ℕ → ℝ,
      PositiveSubexponentialPrefactor Aratio ∧
        ∀ᶠ n in atTop,
          ∀ᶠ M in atTop,
            freeQ2BoundaryProfileOfBeta β hβpos n ≤
              Aratio n *
                freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos M n


def
    FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ᶠ n in atTop,
        ∀ᶠ M in atTop,
          freeQ2BoundaryProfileOfBeta β hβpos n ≤
            C * (n : ℝ) ^ k *
              freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos M n


def
    FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∃ (outerScale : ℕ → ℕ) (C : ℝ) (k : ℕ), 0 < C ∧
      (∀ᶠ n in atTop, n ≤ outerScale n) ∧
        ∀ᶠ n in atTop,
          freeQ2BoundaryProfileOfBeta β hβpos n ≤
            C * (n : ℝ) ^ k *
              freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos
                (outerScale n) n


end Exact3D
end StatMech
