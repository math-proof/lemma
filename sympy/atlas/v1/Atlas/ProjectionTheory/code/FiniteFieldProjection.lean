/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FiniteFieldProjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.ZMod.Basic

namespace FiniteFieldProjection

open Finset

/-- Projection of a point `x = (x₁, x₂) ∈ 𝔽_p²` onto the direction `θ`:
`π_θ(x) = x₁ + θ · x₂`. -/
def piTheta {p : ℕ} (θ : ZMod p) : ZMod p × ZMod p → ZMod p :=
  fun x => x.1 + θ * x.2


/--
Conjecture 2.1 (finite field projection conjecture). For some absolute constant
`C`, if `X ⊂ 𝔽_p²`, `D ⊂ 𝔽_p`, and `S = max_{θ ∈ D} |π_θ(X)| ≤ p/2`, then
$$|D| \;\lesssim\; \frac{S^2}{|X|},$$
equivalently `|D| · |X| ≤ C · S²`. This is the finite-field analogue of the
Szemerédi-Trotter projection bound and is open in general.
-/
end FiniteFieldProjection
