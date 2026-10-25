/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/FlowSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Real Set MeasureTheory


noncomputable section

namespace ODEFlow

/-- A spacetime point in $\mathbb{R}^{1+n}$. -/
abbrev Spacetime (n : ℕ) := Fin (n + 1) → ℝ

/-- A real-valued scalar field on $\mathbb{R}^{1+n}$. -/
abbrev ScalarField (n : ℕ) := Spacetime n → ℝ

/-- A vector field on $\mathbb{R}^{1+n}$, i.e. a map from spacetime points to vectors. -/
abbrev VectorField (n : ℕ) := Spacetime n → Spacetime n

/-- A spacetime metric: at each point of $\mathbb{R}^{1+n}$, a function
$m_{\mu\nu}$ on pairs of indices. -/
abbrev Metric (n : ℕ) := Spacetime n → Fin (n + 1) → Fin (n + 1) → ℝ

end ODEFlow
end
