/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM19/BurgersSingularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM19.TransportBurgers
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM19.TransportBurgers
set_option maxHeartbeats 1600000

open Finset MeasureTheory Set


noncomputable section

namespace TransportBurgers

/-- Predicate that a pair of curves $g_0, g_1 : \mathbb{R} \to \mathbb{R}$
forms a Burger's characteristic: $g_0'(s) = 1$ and $g_1'(s) = u(g_0(s), g_1(s))$. -/
def IsBurgersCharacteristic (u : ℝ → ℝ → ℝ) (g0 g1 : ℝ → ℝ) : Prop :=
  (∀ s, deriv g0 s = 1) ∧ (∀ s, deriv g1 s = u (g0 s) (g1 s))

end TransportBurgers
end
