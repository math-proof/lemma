/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM18/LagrangianMechanics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Real Set MeasureTheory


noncomputable section

namespace CM18

/-- Spacetime $\mathbb{R}^{1+n}$ modeled as functions $\text{Fin}(n+1) \to \mathbb{R}$.
The component indexed by $0$ is time and components $1, \ldots, n$ are spatial. -/
abbrev Spacetime (n : ℕ) := Fin (n + 1) → ℝ

/-- A real-valued scalar field on $(1+n)$-dimensional spacetime. -/
abbrev ScalarField (n : ℕ) := Spacetime n → ℝ

end CM18
end
