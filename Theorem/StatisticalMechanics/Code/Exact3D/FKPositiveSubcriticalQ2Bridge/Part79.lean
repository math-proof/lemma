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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part81
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexDecrementedSourceAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  refine
    finiteBoundaryGhostDecrementedSourceWeightCutoffSum_le_of_vertexCutoffSum_le
      (A := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n)
      (C := finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n)
      β H n Ω ?_ ?_
  · exact hn H hH Ω
  · exact
      (finiteBoundaryGhostSimonCollapsedDenominatorProduct_eq_boundary_sum_vertexProduct
        β H n).ge


end Exact3D
end StatMech
