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
public import Abbrev.v1.Atlas.DifferentialAnalysis.code.Integration

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set

namespace LebesgueIntegration

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Integrability on `E` for an `EReal`-valued function: both the positive and the
negative parts have finite Lebesgue integral over `E`. -/
def integrableOnEReal (f : X → EReal) (E : Set X) (μ : Measure X := by volume_tac) : Prop :=
  ∫⁻ x in E, (f x).toENNReal ∂μ ≠ ⊤ ∧ ∫⁻ x in E, (-f x).toENNReal ∂μ ≠ ⊤

end LebesgueIntegration
end
