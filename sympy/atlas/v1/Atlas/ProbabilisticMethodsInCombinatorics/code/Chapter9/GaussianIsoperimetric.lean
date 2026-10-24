/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/GaussianIsoperimetric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory

noncomputable section

namespace GaussianIsoperimetric

/-- A set $H \subseteq E$ is a half-space if it has the form $\{x : \langle v, x \rangle \leq c\}$
for some nonzero $v$ and real $c$. -/
def IsHalfSpace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : Set E) : Prop :=
  ∃ (v : E) (_ : v ≠ 0) (c : ℝ), H = {x | @inner ℝ _ _ v x ≤ c}


/-- Gaussian isoperimetric inequality (Theorem 9.4.15): among all measurable sets $A$ of a
given standard Gaussian measure, half-spaces minimize the Gaussian measure of the
$t$-thickening. That is, if $\gamma(A) = \gamma(H)$ for a half-space $H$, then
$\gamma(A_t) \geq \gamma(H_t)$ for every $t \geq 0$. -/
end GaussianIsoperimetric
