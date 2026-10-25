/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM6/HeatSymmetryEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Basic
open MeasureTheory Real Filter Set
open scoped ENNReal


noncomputable section

namespace CM6

/-- The total thermal energy of $u$ at time $t$ (Definition 2.0.2):
$\mathcal{T}(t) = \int_{\mathbb{R}^n} u(t, x)\, d^n x$. -/
def totalThermalEnergy {n : ℕ} (u : ℝ → (Fin n → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ x, u t x

end CM6
end
