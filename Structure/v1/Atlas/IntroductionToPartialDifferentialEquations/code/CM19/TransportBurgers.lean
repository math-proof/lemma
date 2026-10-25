/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM19/TransportBurgers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM19.TransportBurgers
open Finset MeasureTheory Set


noncomputable section

namespace TransportBurgers

/-- **Definition 2.0.1 (Characteristic curves).** A characteristic curve for
Burger's equation with solution $u$ is a pair $(\gamma_t, \gamma_x) : \mathbb{R} \to
\mathbb{R}^2$ satisfying the ODE system
$$\frac{d}{ds} \gamma_t(s) = 1, \qquad
\frac{d}{ds} \gamma_x(s) = u(\gamma_t(s), \gamma_x(s)).$$ -/
structure BurgersCharacteristic (u : ℝ → ℝ → ℝ) (γ_t γ_x : ℝ → ℝ) : Prop where
  time_param : ∀ s, deriv γ_t s = 1
  space_param : ∀ s, deriv γ_x s = u (γ_t s) (γ_x s)

end TransportBurgers
end
