/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ProductFormula.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Complex
import Mathlib.Analysis.Normed.Field.ProperSpace
import Theorem.v1.Atlas.NumberTheoryI.code.ProductFormula


noncomputable section

open MeasureTheory Measure TopologicalSpace Pointwise Filter Topology

open MeasureTheory MeasureTheory.Measure Metric Pointwise in
def IsNormalizedAbsVal
    {K : Type*} [Field K] [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [LocallyCompactSpace K] [T2Space K]
    (f : K → ℝ) : Prop :=
  (∀ a, 0 ≤ f a) ∧
  ∀ (μ : Measure K) [μ.IsAddHaarMeasure] (a : K) (S : Set K),
    μ ((a * ·) '' S) = ENNReal.ofReal (f a) * μ S

end
