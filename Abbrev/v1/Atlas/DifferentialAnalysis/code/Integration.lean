/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Integration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Data.Real.ConjExponents
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Data.EReal.Operations


@[expose] public noncomputable section

open MeasureTheory ENNReal Set

namespace Integration

variable {X : Type*} [MeasurableSpace X]

/-- The Lebesgue integral of a nonnegative `ENNReal`-valued function over a set `E`
with respect to a measure `μ`. -/
abbrev lebesgueIntegralNonneg (μ : Measure X) (f : X → ENNReal) (E : Set X) : ENNReal :=
  ∫⁻ x in E, f x ∂μ

end Integration
end
