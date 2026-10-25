/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM3/HeatUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM3.HeatUniqueness
open MeasureTheory Measure Set


noncomputable section

namespace HeatUniqueness

/-- The $L^2$ energy of $w(t, \cdot)$ on $[0, L]$ at time $t$:
$E(t) = \int_0^L w(t, x)^2\, dx$. Used in the energy-method uniqueness proof. -/
def energy (w : ℝ → ℝ → ℝ) (L : ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..L, (w t x) ^ 2

end HeatUniqueness
end
