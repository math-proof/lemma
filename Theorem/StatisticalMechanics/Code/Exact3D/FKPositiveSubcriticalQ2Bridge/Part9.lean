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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part9
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    freeQ2BoundaryProfileSubexpSameMass_of_boundaryVertexEnvelope
    (hprofile :
      FreeQ2BoundaryProfileBoundaryVertexEnvelopeForFixedInnerSameMassPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
  intro β hβpos hβc Alo AfkHi mass hmass hconn
  rcases hprofile β hβpos hβc Alo AfkHi mass hmass hconn with
    ⟨Apoint, Acount, hApoint, hAcount, hcount, hpoint⟩
  refine
    ⟨fun n => Acount n * Apoint n,
      PositiveSubexponentialPrefactor.mul hAcount hApoint, ?_⟩
  have hprofileFromPoint :=
    eventually_freeQ2BoundaryProfileOfBeta_le_card_mul_of_eventually_boundary
      hβpos hpoint
  filter_upwards [hprofileFromPoint, hcount, hApoint.1]
    with n hprofile_n hcount_n hApoint_pos
  have hpoint_nonneg :
      0 ≤ Apoint n * Real.exp (-(mass * (n : ℝ))) := by
    exact mul_nonneg (le_of_lt hApoint_pos) (Real.exp_pos _).le
  calc
    freeQ2BoundaryProfileOfBeta β hβpos n
        ≤ ((Finset.univ.filter
            (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)).card : ℝ) *
            (Apoint n * Real.exp (-(mass * (n : ℝ)))) :=
      hprofile_n
    _ ≤ Acount n * (Apoint n * Real.exp (-(mass * (n : ℝ)))) :=
      mul_le_mul_of_nonneg_right hcount_n hpoint_nonneg
    _ = (Acount n * Apoint n) * Real.exp (-(mass * (n : ℝ))) := by
      ring


end Exact3D
end StatMech
