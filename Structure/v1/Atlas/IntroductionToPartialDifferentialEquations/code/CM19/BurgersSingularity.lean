/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM19/BurgersSingularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM19.TransportBurgers
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM19.TransportBurgers
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM19.BurgersSingularity
set_option maxHeartbeats 1600000

open Finset MeasureTheory Set


noncomputable section

namespace TransportBurgers

/-- Bundled (paired) version of a Burger's characteristic curve
$\gamma : \mathbb{R} \to \mathbb{R} \times \mathbb{R}$: the time component
has derivative $1$ and the space component has derivative $u(\gamma_t, \gamma_x)$. -/
structure IsCharacteristicCurve (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ) : Prop where
  time_param : ∀ s, HasDerivAt (fun s => (γ s).1) 1 s
  spatial_eq : ∀ s, HasDerivAt (fun s => (γ s).2) (u (γ s).1 (γ s).2) s

end TransportBurgers
end
