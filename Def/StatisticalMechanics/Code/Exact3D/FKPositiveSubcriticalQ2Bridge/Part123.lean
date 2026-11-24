module
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
public import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
public import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
public import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
public import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
public import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
public import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
public import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part120
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

def FreeQ2ProfilePrefactorCombinationPositiveSubcritical : Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ AfkHi AprofHi : ℕ → ℝ,
      ∃ Ahi : ℕ → ℝ,
        (∀ᶠ n in atTop, 0 < Ahi n) ∧
        Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop
          (nhds 0) ∧
        ∀ᶠ n in atTop, AfkHi n + AprofHi n ≤ Ahi n


def FreeQ2ProfileSeparatePositiveSubcritical : Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    FreeIsingXAxisThermodynamicLimitToFiniteVolumes β ∧
      ∃ (Alo AfkHi AprofHi Ahi : ℕ → ℝ) (mass : ℝ), 0 < mass ∧
        FKXAxisConnectionTwoSidedSubexponentialBounds
          (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo AfkHi
          mass ∧
        (∀ᶠ n in atTop, 0 < Ahi n) ∧
        Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) atTop
          (nhds 0) ∧
        (∀ᶠ n in atTop,
          freeQ2BoundaryProfileOfBeta β hβpos n ≤
            AprofHi n * Real.exp (-(mass * (n : ℝ)))) ∧
        ∀ᶠ n in atTop, AfkHi n + AprofHi n ≤ Ahi n


end Exact3D
end StatMech
