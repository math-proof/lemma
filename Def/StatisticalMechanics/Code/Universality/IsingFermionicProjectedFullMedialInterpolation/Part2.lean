/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialRegularity.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part7
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiscreteInterpolation.Part4
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicProjectedFullMedialInterpolation.Part3
open Filter Metric Set Topology


noncomputable section

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC


namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


noncomputable def StableFullMedialInterpolation.ofTensorTent
    (tangent : ∀ n, A.M n → Complex)
    (F : Nat → Complex → Complex)
    (hcontinuous : ∀ n, Continuous (F n))
    (hprojected : ∀ n e,
      isingProj (tangent n e) (F n (A.medialEmbedding n e)) =
        @FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e)
    (hholder : MeshUniformFullHolder F) :
    A.StableFullMedialInterpolation tangent where
  interpolant := F
  continuousOn n := (hcontinuous n).continuousOn
  projectedMedial := hprojected
  compactEquicontinuous K _hK _hKU :=
    hholder.equicontinuous.equicontinuousOn K


noncomputable def BoundaryRadialTensorTentGeometry.toStableFullMedialInterpolation
    (G : BoundaryRadialTensorTentGeometry A)
    (H : MeshUniformFullHolder
      (BoundaryRadialTensorTentGeometry.interpolant A G)) :
    A.StableFullMedialInterpolation
      (BoundaryRadialTensorTentGeometry.tangent A G) :=
  StableFullMedialInterpolation.ofTensorTent A
    (BoundaryRadialTensorTentGeometry.tangent A G)
    (BoundaryRadialTensorTentGeometry.interpolant A G)
    (BoundaryRadialTensorTentGeometry.interpolant_continuous A G)
    (BoundaryRadialTensorTentGeometry.projectedMedial A G) H

variable {tangent : ∀ n, A.M n → Complex}

variable (I : A.StableFullMedialInterpolation tangent)

def StableFullMedialInterpolation.HasCompactLocalBounds : Prop :=
  ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
    ∃ C : Real, ∀ n z, z ∈ K → ‖I.interpolant n z‖ ≤ C


end FKIsingCaratheodoryApproximation
end StatMech.Universality
end
