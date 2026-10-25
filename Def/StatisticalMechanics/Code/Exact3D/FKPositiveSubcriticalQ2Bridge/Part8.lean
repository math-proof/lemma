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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part7
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

def FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ (Alo AfkHi : ℕ → ℝ) (mass : ℝ),
      0 < mass →
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo AfkHi mass →
      ∃ AprofHi : ℕ → ℝ,
        PositiveSubexponentialPrefactor AprofHi ∧
          ∀ᶠ n in atTop,
            freeQ2BoundaryProfileOfBeta β hβpos n ≤
              AprofHi n * Real.exp (-(mass * (n : ℝ)))


def
    FreeQ2BoundaryProfilePointwiseEnvelopeForFixedInnerSameMassPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ (Alo AfkHi : ℕ → ℝ) (mass : ℝ),
      0 < mass →
      FKXAxisConnectionTwoSidedSubexponentialBounds
        (freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos) Alo AfkHi mass →
      ∃ (Apoint Aenv envelope : ℕ → ℝ),
        PositiveSubexponentialPrefactor Apoint ∧
          PositiveSubexponentialPrefactor Aenv ∧
          (∀ᶠ n in atTop,
            freeQ2BoundaryProfileOfBeta β hβpos n ≤
              Apoint n * envelope n) ∧
          ∀ᶠ n in atTop,
            envelope n ≤ Aenv n * Real.exp (-(mass * (n : ℝ)))


end Exact3D
end StatMech
