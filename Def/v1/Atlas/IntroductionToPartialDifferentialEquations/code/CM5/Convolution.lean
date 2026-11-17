/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM5/Convolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

open MeasureTheory


noncomputable section

namespace HeatFundamental

/-- The convolution of two functions $f, g : \mathbb{R}^n \to \mathbb{R}$
(Definition 1.1.1): $(f * g)(x) = \int_{\mathbb{R}^n} f(y)\, g(x - y)\, d^n y$. -/
def convolution {n : ℕ} (f g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y : Fin n → ℝ, f y * g (x - y)

end HeatFundamental
end
