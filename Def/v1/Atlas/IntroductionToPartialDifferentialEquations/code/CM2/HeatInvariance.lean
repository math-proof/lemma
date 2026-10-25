/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM2/HeatInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.FDeriv.Basic
open Finset


noncomputable section

namespace HeatEquationInvariance

/-- The (spatial) Laplacian of $f : \mathbb{R}^n \to \mathbb{R}$ at $x$, defined as
$\Delta f(x) = \sum_{i=1}^{n} \partial_i^2 f(x)$. -/
def laplacian {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, deriv (fun h => deriv (fun xi => f (Function.update x i xi)) (x i + h)) 0

/-- The heat operator $\partial_t u - D\,\Delta u$ applied to $u$ at $(t, x)$,
where $D > 0$ is the diffusion constant. -/
def heatOperator {n : ℕ} (D : ℝ) (u : ℝ → (Fin n → ℝ) → ℝ) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  deriv (fun s => u s x) t - D * laplacian (u t) x

end HeatEquationInvariance
end
