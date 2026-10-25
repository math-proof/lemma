/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryCompactAverage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryAverage
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareCaratheodory.Part5


namespace StatMech.Universality

open Filter Set Topology Metric

noncomputable section

theorem fkIsingExpandingBoundarySquare_normalizedInterpolant_differentiable
    (k : Nat) :
    Differentiable Complex
      (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
        k) := by
  change Differentiable Complex (fun z ↦
    fkIsingSquareBoundaryPerturbedHolomorphicInterpolant
        (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
        (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) z /
      (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex))
  exact
    (fkIsingSquareBoundaryPerturbedHolomorphicInterpolant_differentiable
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k)
      (fkIsingExpandingSquareScale_pos k)).div_const _


theorem fkIsingExpandingBoundarySquare_normalizedInterpolant_holomorphic :
    ∀ k, DifferentiableOn Complex
      (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
        k) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U :=
  fun k ↦
    (fkIsingExpandingBoundarySquare_normalizedInterpolant_differentiable k).differentiableOn


end
end StatMech.Universality
