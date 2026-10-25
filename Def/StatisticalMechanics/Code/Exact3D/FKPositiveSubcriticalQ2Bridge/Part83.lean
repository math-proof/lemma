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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part80
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyGlobalDecrementedSourceAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        Summable (finiteBoundaryGhostDecrementedSourceWeightSummand β H n) ∧
          (∑' m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ,
              finiteBoundaryGhostDecrementedSourceWeightSummand β H n m) ≤
            finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaDecrementedSourceAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        Summable (finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n) ∧
          (∑' a : Sigma (finiteBoundaryGhostDecrementedSourceWeightFiber n),
              finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a) ≤
            finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n


def
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaFiniteSubcaseAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset (Sigma (finiteBoundaryGhostDecrementedSourceWeightFiber n)),
          (∑ a ∈ Ω,
              finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a) ≤
            finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n


end Exact3D
end StatMech
