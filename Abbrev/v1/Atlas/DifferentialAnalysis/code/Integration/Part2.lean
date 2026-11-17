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
public import Def.v1.Atlas.DifferentialAnalysis.code.Integration


@[expose] public noncomputable section

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
