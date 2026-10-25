/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM24/Burger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod


noncomputable section

namespace Burger

/-- A function $u(t, x)$ is a (classical) solution of Burger's equation
$\partial_t u + u\,\partial_x u = 0$ if it is $C^1$ and satisfies the PDE pointwise. -/
def IsBurgerSolution (u : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 (Function.uncurry u) ∧
    ∀ t x, deriv (fun t' => u t' x) t + u t x * deriv (fun x' => u t x') x = 0

/-- A pair $(\gamma_0, \gamma_1)$ is a characteristic curve of Burger's equation if
$\frac{d}{ds}\gamma_0 = 1$ and $\frac{d}{ds}\gamma_1 = u(\gamma_0(s), \gamma_1(s))$
(Definition 2.0.1). -/
def IsCharacteristicCurve (u : ℝ → ℝ → ℝ) (γ₀ γ₁ : ℝ → ℝ) : Prop :=
  (∀ s, deriv γ₀ s = 1) ∧ (∀ s, deriv γ₁ s = u (γ₀ s) (γ₁ s))

end Burger
end
