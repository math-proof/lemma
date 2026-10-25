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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part101
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSumPositiveSubcritical_of_eventually_at
    (hsimon :
      ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          FreeQ2BoundaryProfileSimonFreeSumAt β hβpos n) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
  intro β hβpos hβc
  simpa [FreeQ2BoundaryProfileSimonFreeSumAt] using
    hsimon β hβpos hβc


theorem freeQ2BoundaryProfileSimonFreeSum_of_finiteFK
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hfinite β hβpos hβc] with n hn
  rw [freeQ2BoundaryProfileOfBeta]
  rw [FK.boxBoundaryConnProfile_eq_wiredFiniteMeasure_real]
  exact hn

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSumAt_of_finiteFKAt
    {β : ℝ} {hβpos : 0 < β} {n : ℕ}
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumAt β hβpos n) :
    FreeQ2BoundaryProfileSimonFreeSumAt β hβpos n := by
  rw [FreeQ2BoundaryProfileSimonFreeSumAt]
  rw [freeQ2BoundaryProfileOfBeta]
  rw [FK.boxBoundaryConnProfile_eq_wiredFiniteMeasure_real]
  exact hfinite


theorem freeQ2BoundaryProfileSimonFreeSum_of_boundaryGhostApprox_firstExitPositive
    (happrox :
      FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical)
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_finiteFK
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_boundaryGhostApprox_firstExitPositive
      happrox hfirst)


end Exact3D
end StatMech
