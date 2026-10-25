/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2R.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic


noncomputable section

open MeasureTheory Metric Set Finset

open scoped Classical InnerProductSpace

namespace ProjectionTheory

/-- The perpendicular direction in $\mathbb{R}^2$: rotates a vector $(e_0, e_1)$ to
$(-e_1, e_0)$. -/
def perpDir (e : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i =>
    if i = (0 : Fin 2) then -(EuclideanSpace.equiv (Fin 2) ℝ e 1)
    else EuclideanSpace.equiv (Fin 2) ℝ e 0)

/-- The rectangle in $\mathbb{R}^2$ centered at `center` with major axis along `dir`,
of half-length `halfLength` along `dir` and half-width `halfWidth` along `perpDir dir`. -/
def rectangleSet (center : EuclideanSpace ℝ (Fin 2))
    (dir : EuclideanSpace ℝ (Fin 2)) (halfWidth halfLength : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | |⟪x - center, dir⟫_ℝ| ≤ halfLength ∧
       |⟪x - center, perpDir dir⟫_ℝ| ≤ halfWidth}

end ProjectionTheory
end
