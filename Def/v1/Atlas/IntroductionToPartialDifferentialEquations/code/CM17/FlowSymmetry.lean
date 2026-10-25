/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/FlowSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM17.FlowSymmetry
open Real Set MeasureTheory


noncomputable section

namespace ODEFlow

/-- The spacetime gradient of a scalar field $\varphi$: the index-$\mu$ component
is the partial derivative $\partial_\mu \varphi$. -/
def spacetimeGradient {n : ℕ} (φ : ScalarField n) (x : Spacetime n) : Fin (n + 1) → ℝ :=
  fun μ => fderiv ℝ φ x (Pi.single μ 1)

/-- The Jacobian of a map $F : \mathbb{R}^{1+n} \to \mathbb{R}^{1+n}$ at $x$:
$(\partial F^\mu / \partial x^\nu)(x)$. -/
def jacobian {n : ℕ} (F : Spacetime n → Spacetime n) (x : Spacetime n) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun μ ν => fderiv ℝ (fun y => F y μ) x (Pi.single ν 1)

/-- The Kronecker delta $\delta_{\mu\nu}$, equal to $1$ if $\mu = \nu$ and $0$ otherwise. -/
def kroneckerDelta (n : ℕ) (μ ν : Fin (n + 1)) : ℝ :=
  if μ = ν then 1 else 0

/-- The (spacetime) divergence of a vector field $Y$: $\nabla \cdot Y = \sum_\alpha \partial_\alpha Y^\alpha$. -/
def divergence {n : ℕ} (Y : VectorField n) (x : Spacetime n) : ℝ :=
  ∑ α : Fin (n + 1), jacobian Y x α α

/-- The Jacobian of a spacetime map packaged as a matrix. -/
def jacobianMatrix {n : ℕ} (G : Spacetime n → Spacetime n) (x : Spacetime n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of (jacobian G x)

/-- A vector field $Y$ has all partial derivatives uniformly bounded by $C > 0$:
$|\partial_\mu Y^\nu(x)| \leq C$ for all $x, \mu, \nu$. -/
def HasBoundedDerivatives {n : ℕ} (Y : VectorField n) (C : ℝ) : Prop :=
  0 < C ∧ ∀ (x : Spacetime n) (μ ν : Fin (n + 1)),
    |fderiv ℝ (fun y => Y y ν) x (Pi.single μ 1)| ≤ C

end ODEFlow
end
