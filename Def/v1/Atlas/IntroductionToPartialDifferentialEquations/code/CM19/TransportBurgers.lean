/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM19/TransportBurgers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Finset MeasureTheory Set


noncomputable section

namespace TransportBurgers

/-- The transport equation $\sum_\mu X^\mu \partial_\mu u = 0$ associated to a
vector field $X$ on $\mathbb{R}^{n+1}$. A function $u$ solves the transport
equation at every point $p$ iff the directional derivative of $u$ along $X(p)$
vanishes. -/
def SolvesTransport {n : ℕ} (X : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (u : (Fin (n + 1) → ℝ) → ℝ) : Prop :=
  ∀ p, ∑ μ : Fin (n + 1), X p μ * fderiv ℝ u p (Pi.single μ 1) = 0

/-- A curve $\gamma : \mathbb{R} \to \mathbb{R}^{n+1}$ is an integral curve of
the vector field $X$ if $\gamma'(s) = X(\gamma(s))$ for all $s$. -/
def IsIntegralCurve {n : ℕ} (X : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (γ : ℝ → (Fin (n + 1) → ℝ)) : Prop :=
  ∀ s, fderiv ℝ γ s 1 = X (γ s)

/-- Burger's equation $u_t + u\,u_x = 0$ in $1 + 1$ dimensions.
A function $u(t, x)$ solves Burger's equation iff the time and space partial
derivatives satisfy this nonlinear conservation law at every spacetime point. -/
def SolvesBurgers (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x, deriv (fun t' => u t' x) t + u t x * deriv (fun x' => u t x') x = 0


end TransportBurgers
end
