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
import Structure.v1.Atlas.ProjectionTheory.code.MainLemma2R


noncomputable section

open MeasureTheory Metric Set Finset

open scoped Classical InnerProductSpace

namespace ProjectionTheory

/-- Realize a `Tube` as the set $\{x \in \mathbb{R}^2 : |\langle x - c, d\rangle| \leq R/2,
\ |\langle x - c, d^\perp\rangle| \leq 1/2\}$. -/
def Tube.asSet (T : Tube) : Set (EuclideanSpace ℝ (Fin 2)) :=
  rectangleSet T.center T.direction (1/2) (T.R/2)

/-- The two-dimensional Fourier transform $\hat f(\xi) = \int f(x) e^{-2\pi i \langle x,
\xi\rangle}\, dx$ of a real-valued function on $\mathbb{R}^2$, returning a complex value. -/
def fourierTransformR2 (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (ξ : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume
    (innerₗ (EuclideanSpace ℝ (Fin 2))) (fun x => (f x : ℂ)) ξ

/-- The set of dyadic scales between $1$ and $R$: $\{2^k : k \in \mathbb{N}, 1 \leq 2^k \leq R\}$. -/
def dyadicScales (R : ℝ) : Set ℝ :=
  {r : ℝ | ∃ k : ℕ, r = 2 ^ k ∧ 1 ≤ r ∧ r ≤ R}

end ProjectionTheory
end
