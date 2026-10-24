/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM19/BurgersSingularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM19.TransportBurgers
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM19.TransportBurgers

set_option maxHeartbeats 1600000

open Finset MeasureTheory Set

noncomputable section

namespace TransportBurgers

/-- Predicate that a pair of curves $g_0, g_1 : \mathbb{R} \to \mathbb{R}$
forms a Burger's characteristic: $g_0'(s) = 1$ and $g_1'(s) = u(g_0(s), g_1(s))$. -/
def IsBurgersCharacteristic (u : ℝ → ℝ → ℝ) (g0 g1 : ℝ → ℝ) : Prop :=
  (∀ s, deriv g0 s = 1) ∧ (∀ s, deriv g1 s = u (g0 s) (g1 s))

/-- Bundled (paired) version of a Burger's characteristic curve
$\gamma : \mathbb{R} \to \mathbb{R} \times \mathbb{R}$: the time component
has derivative $1$ and the space component has derivative $u(\gamma_t, \gamma_x)$. -/
structure IsCharacteristicCurve (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ) : Prop where
  time_param : ∀ s, HasDerivAt (fun s => (γ s).1) 1 s
  spatial_eq : ∀ s, HasDerivAt (fun s => (γ s).2) (u (γ s).1 (γ s).2) s
