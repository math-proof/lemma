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
public import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part7
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

theorem freeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical_trivial :
    FreeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical := by
  intro β hβpos _hβc _Alo _AfkHi mass _hmass _hconn
  refine
    ⟨fun n =>
      freeQ2BoundaryProfileOfBeta β hβpos n *
        Real.exp (mass * (n : ℝ)), ?_⟩
  exact Eventually.of_forall fun n => by
    have hexp :
        Real.exp (mass * (n : ℝ)) *
            Real.exp (-(mass * (n : ℝ))) = 1 := by
      rw [← Real.exp_add]
      rw [show mass * (n : ℝ) + -(mass * (n : ℝ)) = 0 by ring,
        Real.exp_zero]
    simp [mul_assoc, hexp]


end Exact3D
end StatMech
