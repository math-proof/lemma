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
import Def.v1.Atlas.DifferentialAnalysis.code.Integration


noncomputable section

open MeasureTheory ENNReal Set

namespace LebesgueIntegration

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Integrability on `E` for a real-valued function, defined via Mathlib's
`IntegrableOn` (Melrose Def 4.1). -/
abbrev integrableOn (f : X → ℝ) (E : Set X) (μ : Measure X := by volume_tac) : Prop :=
  MeasureTheory.IntegrableOn f E μ

/-- The signed Lebesgue integral of a real-valued function over `E` with respect to
`μ` (Melrose Def 4.4). -/
abbrev signedIntegral (f : X → ℝ) (E : Set X) (μ : Measure X := by volume_tac) : ℝ :=
  ∫ x in E, f x ∂μ

end LebesgueIntegration

namespace NormedSpaces

/-- A `𝕜`-normed space `V` is a Banach space iff it is complete. -/
abbrev IsBanachSpace (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (V : Type*) [NormedAddCommGroup V] [NormedSpace 𝕜 V] : Prop := CompleteSpace V

end NormedSpaces
end
