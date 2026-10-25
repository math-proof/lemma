/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryHolderDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryCompactAverage.Part2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Hull


namespace StatMech.Universality

open Set Metric

noncomputable section

theorem fkIsingExpandingBoundarySquare_carrier_isCompact (k : Nat) :
    IsCompact
      (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) := by
  change IsCompact {z : Complex | ∃ a : FKIsingSquareWiredCarrier
      (fkIsingExpandingSquareSide k),
    dist z (fkIsingSquareWiredPerturbedCarrierPosition
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) a) ≤
        fkIsingExpandingSquareMesh k}
  rw [show {z : Complex | ∃ a : FKIsingSquareWiredCarrier
      (fkIsingExpandingSquareSide k),
    dist z (fkIsingSquareWiredPerturbedCarrierPosition
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) a) ≤
        fkIsingExpandingSquareMesh k} =
      ⋃ a : FKIsingSquareWiredCarrier (fkIsingExpandingSquareSide k),
        closedBall (fkIsingSquareWiredPerturbedCarrierPosition
          (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
          (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) a)
          (fkIsingExpandingSquareMesh k) by
      ext z
      simp [mem_closedBall]]
  exact isCompact_iUnion fun _ ↦ isCompact_closedBall _ _


theorem exists_fkIsingExpandingBoundarySquare_scaleDerivativeBound :
    ∃ C : Nat → NNReal, ∀ k z,
      z ∈ convexHull Real
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) →
      ‖deriv
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
          k) z‖₊ ≤ C k := by
  choose R hR using fun k ↦
    (fkIsingExpandingBoundarySquare_carrier_isCompact k).isBounded.subset_closedBall
      (0 : Complex)
  let F : Nat → Complex → Complex := fun k ↦
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k
  have hcontinuous : ∀ k, Continuous (fun z ↦ ‖deriv (F k) z‖₊) := by
    intro k
    exact continuous_nnnorm.comp
      ((fkIsingExpandingBoundarySquare_normalizedInterpolant_differentiable k).contDiff
        (n := 1)).continuous_deriv_one
  have hHull : ∀ k, convexHull Real
      (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) ⊆
        closedBall 0 (R k) := by
    intro k
    exact convexHull_min (hR k) (convex_closedBall 0 (R k))
  have hbdd : ∀ k, BddAbove
      ((fun z ↦ ‖deriv (F k) z‖₊) '' closedBall 0 (R k)) := by
    intro k
    exact (isCompact_closedBall 0 (R k)).bddAbove_image
      (hcontinuous k).continuousOn
  choose C hC using fun k ↦ bddAbove_def.mp (hbdd k)
  refine ⟨C, ?_⟩
  intro k z hz
  apply hC k
  exact ⟨z, hHull k hz, rfl⟩


theorem exists_fkIsingExpandingBoundarySquare_scaleLipschitzBound :
    ∃ C : Nat → NNReal, ∀ k,
      LipschitzOnWith (C k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k)
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) := by
  obtain ⟨C, hC⟩ := exists_fkIsingExpandingBoundarySquare_scaleDerivativeBound
  refine ⟨C, ?_⟩
  intro k
  let carrier :=
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k
  exact (convex_convexHull Real carrier).lipschitzOnWith_of_nnnorm_deriv_le
      (fun z _hz ↦
        fkIsingExpandingBoundarySquare_normalizedInterpolant_differentiable k z)
      (fun z hz ↦ hC k z hz) |>.mono
        (subset_convexHull Real carrier)


end
end StatMech.Universality
