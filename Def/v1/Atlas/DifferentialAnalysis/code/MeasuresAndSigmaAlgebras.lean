/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.OuterMeasure.Caratheodory
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Content
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.MetricSpace.Basic
import Structure.v1.Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras
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
