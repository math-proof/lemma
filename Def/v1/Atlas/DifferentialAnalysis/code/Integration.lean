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
import Abbrev.v1.Atlas.DifferentialAnalysis.code.Integration


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
