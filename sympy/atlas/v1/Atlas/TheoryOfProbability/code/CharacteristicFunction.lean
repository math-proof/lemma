/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CharacteristicFunction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

open MeasureTheory Complex

namespace ProbabilityTheory

/-- The **characteristic function** of a probability measure `μ` on `ℝ`, defined by
`φ(t) = ∫ exp(i t x) dμ(x)`. For a random variable `X` with law `μ` this is
`φ_X(t) = E[exp(i t X)]`. -/
noncomputable def charFun (μ : Measure ℝ) (t : ℝ) : ℂ :=
  ∫ x, Complex.exp (Complex.I * ↑t * ↑x) ∂μ
