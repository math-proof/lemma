/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM18/NoetherEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM18.LagrangianMechanics
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM18.LagrangianMechanics
open Real Set MeasureTheory


noncomputable section

namespace CM18

/-- A metric on $(1+n)$-dimensional spacetime: a function assigning to each spacetime point $x$ a
matrix of components $m_{\mu\nu}(x)$ for $\mu,\nu \in \{0,1,\dots,n\}$. -/
abbrev Metric (n : ℕ) := Spacetime n → Fin (n + 1) → Fin (n + 1) → ℝ

/-- An inverse metric on $(1+n)$-dimensional spacetime: a function assigning to each spacetime
point $x$ a matrix of components $(m^{-1})^{\mu\nu}(x)$ for $\mu,\nu \in \{0,1,\dots,n\}$. -/
abbrev InverseMetric (n : ℕ) := Spacetime n → Fin (n + 1) → Fin (n + 1) → ℝ

end CM18
end
