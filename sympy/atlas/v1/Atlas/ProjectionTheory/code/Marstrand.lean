/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/Marstrand.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open MeasureTheory Set Real

namespace Marstrand

/-- The unit direction vector $(\cos\theta, \sin\theta) \in \mathbb{R}^2$ associated
to the angle $\theta$. -/
noncomputable def directionVector (θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (![cos θ, sin θ])

/-- Orthogonal projection $\pi_\theta : \mathbb{R}^2 \to \mathbb{R}$ onto the line
through the origin in direction $\theta$, expressed as the continuous linear functional
$x \mapsto \langle x, (\cos\theta, \sin\theta) \rangle$. -/
noncomputable def orthProjLine (θ : ℝ) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  innerSL ℝ (directionVector θ)


/-- **Marstrand's projection theorem (1954).** If $X \subseteq \mathbb{R}^2$ is compact,
then for almost every angle $\theta \in [0, \pi)$ the Hausdorff dimension of the
orthogonal projection $\pi_\theta(X)$ onto the line in direction $\theta$ equals
$\min(\dim_H X, 1)$. -/
end Marstrand
