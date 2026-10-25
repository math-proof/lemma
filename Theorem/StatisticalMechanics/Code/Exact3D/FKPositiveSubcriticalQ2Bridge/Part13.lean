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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part13
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_at
    (hcompare :
      ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisAt β hβpos n) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  exact hcompare β hβpos hβc


theorem freeQ2BoundaryProfileDoubleScaleAt_of_vertexDoubleScaleAt
    (β : ℝ) (hβpos : 0 < β) (n : ℕ)
    (hpoint :
      FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisAt β hβpos n) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisAt β hβpos n :=
  freeQ2BoundaryProfileOfBeta_le_card_mul_of_forall_boundary hβpos n
    (fun v hv => hpoint v hv)


theorem
    freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_vertex_at
    (hpoint :
      ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisAt β hβpos n) :
    FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hpoint β hβpos hβc] with n hpoint_n
  exact freeQ2BoundaryProfileDoubleScaleAt_of_vertexDoubleScaleAt β hβpos n
    hpoint_n


end Exact3D
end StatMech
