/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareGridConsistency.Part4


namespace StatMech.Universality

open Filter Finset Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem isingFiniteWeightedBoundaryError_le
    {V : Type*} [Fintype V] [Nonempty V]
    (boundary : V → Prop) (data target : V → Real) (bound : Real)
    (hbound : 0 ≤ bound)
    (hboundary : ∀ x, boundary x → |data x - target x| ≤ bound) :
    isingFiniteWeightedBoundaryError boundary data target ≤ bound := by
  classical
  unfold isingFiniteWeightedBoundaryError
  rw [Finset.max'_le_iff]
  intro z hz
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz
  by_cases hx : boundary x
  · simpa [hx] using hboundary x hx
  · simp [hx, hbound]

theorem isingFiniteWeightedTargetResidual_le
    {V : Type*} [Fintype V] [Nonempty V]
    (conductance : V → V → Real) (boundary : V → Prop)
    (target : V → Real) (bound : Real) (hbound : 0 ≤ bound)
    (hresidual : ∀ x, ¬ boundary x →
      |isingFiniteWeightedLaplacian conductance target x| ≤ bound) :
    isingFiniteWeightedTargetResidual conductance boundary target ≤ bound := by
  classical
  unfold isingFiniteWeightedTargetResidual
  rw [Finset.max'_le_iff]
  intro z hz
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz
  by_cases hx : boundary x
  · simp [hx, hbound]
  · simpa [hx] using hresidual x hx

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
