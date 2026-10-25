/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Lagrangian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Real Set MeasureTheory


noncomputable section

namespace CM17Lagrangian

/-- Spacetime $\mathbb{R}^{1+n}$ as the function type $\{0, 1, \ldots, n\} \to \mathbb{R}$.
The index $0$ is the time coordinate; indices $1, \ldots, n$ are spatial. -/
abbrev Spacetime (n : ℕ) := Fin (n + 1) → ℝ

/-- A scalar field on $\mathbb{R}^{1+n}$, i.e. a real-valued function
$\phi : \mathbb{R}^{1+n} \to \mathbb{R}$. -/
abbrev ScalarField (n : ℕ) := Spacetime n → ℝ

end CM17Lagrangian
end
