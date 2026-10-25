/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Integration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.EReal.Operations


noncomputable section

open MeasureTheory ENNReal Set

namespace Integration

variable {X : Type*} [MeasurableSpace X]

/-- The Lebesgue integral of a nonnegative `ℝ≥0∞`-valued function over a set `E`
with respect to a measure `μ`. -/
abbrev lebesgueIntegralNonneg (μ : Measure X) (f : X → ℝ≥0∞) (E : Set X) : ℝ≥0∞ :=
  ∫⁻ x in E, f x ∂μ

end Integration
end
