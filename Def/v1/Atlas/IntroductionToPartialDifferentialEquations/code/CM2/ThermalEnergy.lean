/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM2/ThermalEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

open MeasureTheory Filter

set_option maxHeartbeats 800000


noncomputable section

namespace HeatEquation

/-- The total thermal energy at time $t$ associated to $u(t, x)$, defined by
$\mathcal{T}(t) \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} u(t, x) \, d^n x$.
(Definition 2.0.2.) -/
def totalThermalEnergy (n : ℕ) (u : ℝ → (Fin n → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ x : Fin n → ℝ, u t x

end HeatEquation
end
