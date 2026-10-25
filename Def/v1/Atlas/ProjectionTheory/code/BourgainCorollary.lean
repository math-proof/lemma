/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BourgainCorollary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace BourgainProjection

open MeasureTheory Real Set

/-- Orthogonal projection of a point $x \in \mathbb{R}^2$ onto the line through the origin
making angle $\theta$ with the $x$-axis: $\pi_\theta(x) = x_0 \cos\theta + x_1 \sin\theta$. -/
noncomputable def orthogonalProjection (θ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  x 0 * Real.cos θ + x 1 * Real.sin θ


/-- The $\delta$-covering number $|A|_\delta$ of a set $A$ in a pseudo-extended metric space,
returned as a real number (via the external covering number from Mathlib). -/
noncomputable def coveringNum (δ : NNReal) {α : Type*} [PseudoEMetricSpace α]
    (A : Set α) : ℝ :=
  ((Metric.externalCoveringNumber δ A).toNat : ℝ)

/-- The average $\delta$-covering number of a one-parameter family of projections
$f_t : \mathbb{R}^2 \to \mathbb{R}$ applied to $X$, averaged over the parameter
$t \in [a,b]$: $\frac{1}{b-a} \int_a^b |f_t(X)|_\delta \, dt$. -/
noncomputable def avgFamilyCovering (f : ℝ → EuclideanSpace ℝ (Fin 2) → ℝ) (δ : NNReal)
    (X : Set (EuclideanSpace ℝ (Fin 2))) (a b : ℝ) : ℝ :=
  (b - a)⁻¹ * (∫ t in Set.Icc a b, coveringNum δ (f t '' X))

/-- The average $\delta$-covering number of the orthogonal projections of $X \subset \mathbb{R}^2$
over angles $\theta \in [0, \pi]$. -/
noncomputable def avgProjectionCovering (δ : NNReal)
    (X : Set (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  avgFamilyCovering orthogonalProjection δ X 0 π

end BourgainProjection
