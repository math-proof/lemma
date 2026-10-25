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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryHolderDerivative.Part2


namespace StatMech.Universality

open Set Metric

noncomputable section

noncomputable def
    fkIsingExpandingBoundarySquare_holderInterpolation_of_deriv_bound
    (C : NNReal)
    (hderiv : ∀ k z,
      z ∈ convexHull Real
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) →
      ‖deriv
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
          k) z‖₊ ≤ C) :
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.HolderInterpolation := by
  refine
    { exponent := 1
      exponent_pos := zero_lt_one
      constant := C
      holder := ?_ }
  intro k
  let carrier :=
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k
  let hull := convexHull Real carrier
  let F :=
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k
  have hF : Differentiable Complex F :=
    fkIsingExpandingBoundarySquare_normalizedInterpolant_differentiable k
  have hLipHull : LipschitzOnWith C F hull :=
    (convex_convexHull Real carrier).lipschitzOnWith_of_nnnorm_deriv_le
      (fun z _hz ↦ hF z)
      (fun z hz ↦ hderiv k z hz)
  exact
    (hLipHull.mono (subset_convexHull Real carrier)).holderOnWith


noncomputable def
    fkIsingExpandingBoundarySquare_holderInterpolation_of_scale_deriv_bound
    (C : Nat → NNReal)
    (hderiv : ∀ k z,
      z ∈ convexHull Real
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) →
      ‖deriv
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
          k) z‖₊ ≤ C k)
    (hC : BddAbove (Set.range C)) :
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.HolderInterpolation := by
  let C₀ : NNReal := Classical.choose (bddAbove_def.mp hC)
  have hC₀ : ∀ y ∈ Set.range C, y ≤ C₀ :=
    Classical.choose_spec (bddAbove_def.mp hC)
  apply fkIsingExpandingBoundarySquare_holderInterpolation_of_deriv_bound C₀
  intro k z hz
  exact (hderiv k z hz).trans (hC₀ (C k) ⟨k, rfl⟩)


end
end StatMech.Universality
