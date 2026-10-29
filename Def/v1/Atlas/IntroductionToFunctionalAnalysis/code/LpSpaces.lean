/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket


noncomputable section

open scoped ENNReal NNReal

open MeasureTheory

namespace LpSpaces

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {E : Type*} [NormedAddCommGroup E]

/-- The $L^p$ (extended) norm of a function $f : α → E$ with respect to the measure $μ$.
For $1 ≤ p < ∞$, this is $\|f\|_p = \left(\int |f|^p \, dμ\right)^{1/p}$, and for $p = ∞$
it is the essential supremum $\|f\|_∞ = \operatorname{ess\,sup}|f|$. This is a thin wrapper
around `MeasureTheory.eLpNorm`. -/
def eLpNorm (f : α → E) (p : ENNReal) (μ : Measure α := by volume_tac) : ENNReal :=
  MeasureTheory.eLpNorm f p μ

/-- The $L^p$ space $L^p(μ; E) = \{f : α → E : f \text{ measurable and } \|f\|_p < ∞\}$,
quotiented by the equivalence relation of almost-everywhere equality. Implemented as a thin
wrapper around `MeasureTheory.Lp`. -/
def Lp (E : Type*) [NormedAddCommGroup E] (p : ENNReal)
    {α : Type*} [MeasurableSpace α] (μ : Measure α) : Type _ :=
  ↥(MeasureTheory.Lp E p μ)

end LpSpaces
end
