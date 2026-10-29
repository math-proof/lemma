/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/OuterMeasureFromFunctional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.Content
import Mathlib.MeasureTheory.OuterMeasure.Induced
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Order
import Def.v1.Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras.Part3
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ContinuousFunctions
import Def.v1.Atlas.DifferentialAnalysis.code.ContinuousFunctions.Part2


noncomputable section

open Set TopologicalSpace MeasureTheory

open scoped ENNReal NNReal Topology ZeroAtInfty

namespace MeasuresAndSigmaAlgebras

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]

/-- A continuous linear functional `u : C₀(X, ℝ) →L[ℝ] ℝ` is *positive* if `u f ≥ 0`
whenever `f ≥ 0` pointwise. -/
def IsPositiveLinearFunctional (u : C₀(X, ℝ) →L[ℝ] ℝ) : Prop :=
  ∀ f : C₀(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ u f

/-- The premeasure of an open set `U` associated to a positive linear functional `u`:
the supremum of `u f` over all `f : C₀(X, ℝ)` with `0 ≤ f ≤ 1` and `tsupport f ⊆ U` compact.
This is the open-set value used to induce an outer measure (Section 1.11 of Melrose). -/
def functionalMeasureOpen (u : C₀(X, ℝ) →L[ℝ] ℝ) (U : Set X) (_ : IsOpen U) : ENNReal :=
  ⨆ (f : C₀(X, ℝ)) (_ : (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧
    IsCompact (tsupport f) ∧ tsupport f ⊆ U),
    ENNReal.ofReal (u f)

end MeasuresAndSigmaAlgebras
end
