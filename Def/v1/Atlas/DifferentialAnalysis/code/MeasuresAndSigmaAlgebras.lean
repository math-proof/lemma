/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.OuterMeasure.Caratheodory
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Content
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.MetricSpace.Basic
public import Structure.v1.Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras

@[expose] public section

open MeasureTheory Set

open scoped ENNReal


namespace MeasuresAndSigmaAlgebras

/-- Conversion from an `IsOuterMeasure` proof to a Mathlib `OuterMeasure` bundle. -/
noncomputable def IsOuterMeasure.toOuterMeasure {X : Type*} {μstar : Set X → ENNReal}
    (h : IsOuterMeasure μstar) : OuterMeasure X where
  measureOf := μstar
  empty := h.empty
  mono hsub := h.mono hsub
  iUnion_nat s _ := (h.iUnion_le s)

/-- Volume of the axis-aligned rectangle `[a, b]` in `ℝⁿ`, defined as the product of
side lengths `b i - a i`. -/
@[simp]
noncomputable def rectangleVolume {n : ℕ} (a b : Fin n → ℝ) : ENNReal :=
  ∏ i, ENNReal.ofReal (b i - a i)


end MeasuresAndSigmaAlgebras
