/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSpatialResidualComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalizedPoissonLinearity.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSpatialResidualComparison


namespace StatMech.Universality

open Filter Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem vertexSpatialTargetResidual_nonneg
    (n : Nat)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real) :
    forall z, 0 <= vertexSpatialTargetResidual n target z := by
  intro z
  classical
  unfold vertexSpatialTargetResidual
  split_ifs <;> positivity

theorem vertexSpatialTargetResidualPotential_nonneg
    (n : Nat)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real) :
    forall z, 0 <= vertexSpatialTargetResidualPotential n target z := by
  exact isingFiniteWeightedSpatialResidualPotential_nonneg
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexSpatialTargetResidual n target)
    (vertexSpatialTargetResidual_nonneg n target)

theorem vertexSpatialTargetResidualPotential_eq_sum_point
    (n : Nat)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real) :
    vertexSpatialTargetResidualPotential n target =
      ∑ z ∈ (Finset.univ :
          Finset (Option (FKIsingSquareFullVertexNode n))),
        vertexSpatialTargetResidual n target z •
          vertexPointPoissonBarrier n z := by
  exact isingFiniteWeightedSpatialResidualPotential_eq_sum_point
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexSpatialTargetResidual n target)

theorem vertexSpatialTargetResidualPotential_le_sum_point_bound
    (n : Nat)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real)
    (x : Option (FKIsingSquareFullVertexNode n))
    (bound : Option (FKIsingSquareFullVertexNode n) -> Real)
    (hbound : forall z, vertexPointPoissonBarrier n z x <= bound z) :
    vertexSpatialTargetResidualPotential n target x <=
      ∑ z ∈ (Finset.univ :
          Finset (Option (FKIsingSquareFullVertexNode n))),
        vertexSpatialTargetResidual n target z * bound z := by
  exact isingFiniteWeightedSpatialResidualPotential_le_sum_point_bound
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexSpatialTargetResidual n target)
    bound x (vertexSpatialTargetResidual_nonneg n target) hbound


theorem vertexDirichlet_target_error_le_spatial_residual
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullVertexNode n) -> Real) :
    forall z, |vertexDirichlet n hn z - target z| <=
      vertexBoundaryConsistencyError n hn target +
        vertexSpatialTargetResidualPotential n target z := by
  apply isingFiniteWeighted_harmonic_approximation_of_spatial_residual
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexDirichlet n hn) target
    (vertexBoundaryConsistencyError n hn target)
    (vertexSpatialTargetResidual n target)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexDirichlet_harmonicOn n hn)
  · intro z hz
    rw [vertexDirichlet_boundary n hn z hz]
    exact isingFiniteWeightedBoundaryError_bound
      (vertexDirichletBoundary n) (vertexGhostPrimitive n hn) target z hz
  · exact vertexSpatialTargetResidual_nonneg n target
  · intro z hz
    simp [vertexSpatialTargetResidual, hz]


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
