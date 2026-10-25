/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM18/FieldTransformation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
open Finset


noncomputable section

namespace FieldTransformation

/-- A spacetime point in $\mathbb{R}^{1+n}$. -/
abbrev Spacetime (n : ℕ) := Fin (n + 1) → ℝ

/-- A real-valued scalar field on $\mathbb{R}^{1+n}$. -/
abbrev ScalarField (n : ℕ) := Spacetime n → ℝ

/-- A spacetime metric: at each point of $\mathbb{R}^{1+n}$, a function
$m_{\mu\nu}$ on pairs of indices. -/
abbrev SpacetimeMetric (n : ℕ) := Spacetime n → Fin (n + 1) → Fin (n + 1) → ℝ

end FieldTransformation
end
