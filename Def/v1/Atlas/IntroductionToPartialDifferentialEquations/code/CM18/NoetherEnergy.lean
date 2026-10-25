/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM18/NoetherEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM18.LagrangianMechanics
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM18.LagrangianMechanics
import Abbrev.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM18.NoetherEnergy
open Real Set MeasureTheory


noncomputable section

namespace CM18

/-- A metric Lagrangian $\mathcal{L}(\phi, \nabla\phi, m)$: a function of a scalar value, a
gradient covector, and a metric matrix, returning a real number. This is the type of Lagrangian
considered in CM18 Section 2 (coordinate-invariant Lagrangians). -/
def MetricLagrangian (n : ℕ) :=
  (φ_val : ℝ) → (gradient : Fin (n + 1) → ℝ) → (metric : Fin (n + 1) → Fin (n + 1) → ℝ) → ℝ

/-- Evaluate a metric Lagrangian on a scalar field $\phi$ and metric $m$ at a spacetime point $x$,
producing $\mathcal{L}(\phi(x), \nabla\phi(x), m(x))$. -/
def MetricLagrangian.eval {n : ℕ} (L : MetricLagrangian n)
    (φ : ScalarField n) (m : Metric n) (x : Spacetime n) : ℝ :=
  L (φ x) (spacetimeGradient φ x) (m x)

end CM18
end
