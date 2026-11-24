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
public import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part8
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

theorem
    freeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical_of_pointwiseEnvelope
    (hprofile :
      FreeQ2BoundaryProfilePointwiseEnvelopeForFixedInnerSameMassPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
  intro β hβpos hβc Alo AfkHi mass hmass hconn
  rcases hprofile β hβpos hβc Alo AfkHi mass hmass hconn with
    ⟨Apoint, Aenv, envelope, hApoint, hAenv, hpoint, henv⟩
  refine
    ⟨fun n => Apoint n * Aenv n,
      PositiveSubexponentialPrefactor.mul hApoint hAenv, ?_⟩
  filter_upwards [hApoint.1, hpoint, henv] with n hApoint_pos hpoint_n henv_n
  calc
    freeQ2BoundaryProfileOfBeta β hβpos n ≤ Apoint n * envelope n :=
      hpoint_n
    _ ≤ Apoint n * (Aenv n * Real.exp (-(mass * (n : ℝ)))) :=
      mul_le_mul_of_nonneg_left henv_n (le_of_lt hApoint_pos)
    _ = (Apoint n * Aenv n) * Real.exp (-(mass * (n : ℝ))) := by
      ring


end Exact3D
end StatMech
