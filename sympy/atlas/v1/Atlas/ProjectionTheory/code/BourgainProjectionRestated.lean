/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BourgainProjectionRestated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ProjectionTheory.code.DeltaRegular

open scoped ENNReal NNReal
open Metric Set Real

namespace BourgainProjection

open DeltaRegular

/-- One-dimensional $\delta$-covering number of $X \subseteq \mathbb{R}$. -/
noncomputable def deltaCoveringNumberR (δ : ℝ) (X : Set ℝ) : ℕ∞ :=
  Metric.externalCoveringNumber δ.toNNReal X

/-- `IsDeltaSRegular1D δ s C D` says that $D \subseteq [0,1]$ is a $(\delta, s, C)$-set on the
line: for every interval $B(x, r)$ with $\delta \leq r \leq 1$,
$|D \cap B(x,r)|_\delta \leq C r^s |D|_\delta$. -/
def IsDeltaSRegular1D (δ s C : ℝ) (D : Set ℝ) : Prop :=
  D ⊆ Icc 0 1 ∧
  ∀ (x : ℝ) (r : ℝ),
    δ ≤ r → r ≤ 1 →
    (deltaCoveringNumberR δ (D ∩ Metric.ball x r) : ℝ≥0∞) ≤
      ENNReal.ofReal (C * r ^ s) * (deltaCoveringNumberR δ D : ℝ≥0∞)

/-- The unit direction vector $(\cos\theta, \sin\theta) \in \mathbb{R}^2$ associated to the
angle $\theta$. -/
noncomputable def directionVector (θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (![cos θ, sin θ])

/-- Orthogonal projection onto the line through the origin in direction $\theta$, viewed as a
continuous linear map $\mathbb{R}^2 \to \mathbb{R}$. -/
noncomputable def orthProjLine (θ : ℝ) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  innerSL ℝ (directionVector θ)


/-- **Bourgain's projection theorem, restated** ($\delta$-discretized form): for any
$t \in (0,2)$ and $s \in (0,1]$ there exist $\varepsilon, \eta > 0$ such that for every
$\delta \in (0,1)$, every $(\delta, t, \delta^{-\eta})$-regular set $X \subset \mathbb{R}^2$
with covering number $|X|_\delta = \delta^{-t}$, and every $(\delta, s, \delta^{-\eta})$-regular
set $D \subseteq [0,1]$ of directions, there exists a direction $\theta \in D$ such that for
every robust subset $X' \subseteq X$ with $|X'|_\delta \geq \delta^\eta |X|_\delta$,
$|\pi_\theta(X')|_\delta \geq \delta^{-t/2 - \varepsilon}$. -/
end BourgainProjection
