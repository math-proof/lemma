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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryHolderDerivative.Part2


namespace StatMech.Universality

open Set Metric

noncomputable section

theorem fkIsingExpandingBoundarySquare_entireSquarePrimitive_deriv_medial
    (k : Nat)
    (e : fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k) :
    deriv (isingFermionicEntireSquarePrimitive
      (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k))
      (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding k e) =
        (@FKIsingDobrushinDomain.normalizedFermionicObservable
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.P k)
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k)
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.decEqM k)
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.dobrushin k)
          (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k) e) ^ 2 := by
  rw [(isingFermionicEntireSquarePrimitive_hasDerivAt
    (fkIsingExpandingBoundarySquare_normalizedInterpolant_differentiable k)
    (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding k e)).deriv]
  rw [fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant_medial]


theorem
    fkIsingExpandingBoundarySquare_scalingLimit_of_deriv_and_dense_primitiveIm
    (C : NNReal)
    (hderiv : forall k z,
      z ∈ convexHull Real
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) ->
      ‖deriv
        (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
          k) z‖₊ ≤ C)
    (target Phi : Complex -> Complex)
    (htarget : DifferentiableOn Complex target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (htarget_ne : target
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2)
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (E : StatMech.FrontierA.CompactExhaustion
      fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
    (hidentifyDense : forall
      (phi psi : Nat -> Nat) (f : Complex -> Complex),
      StrictMono phi -> StrictMono psi ->
      TendstoLocallyUniformlyOn
        (fun k =>
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
            (phi (psi k))) f Filter.atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ->
      exists (S : Set Complex) (C : Real), Dense S ∧
        Set.EqOn
          (fun z => (isingFermionicEntireSquarePrimitive f z).im)
          (fun z => (Phi z).im + C) S ∧
        f fkIsingExpandingBoundarySquareCaratheodoryApproximation.root =
          target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) :
    TendstoLocallyUniformlyOn
        fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant
        target Filter.atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ∧
      TendstoLocallyUniformlyOn
        (deriv ∘
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant)
        (deriv target) Filter.atTop
          fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
  exact
    fkIsingExpandingBoundarySquare_scalingLimit_of_holder_and_dense_primitiveIm
      (fkIsingExpandingBoundarySquare_holderInterpolation_of_deriv_bound
        C hderiv)
      target Phi htarget htarget_ne hPhi hPhideriv E hidentifyDense

end
end StatMech.Universality
