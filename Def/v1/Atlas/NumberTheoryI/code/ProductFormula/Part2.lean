/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ProductFormula.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Complex
public import Mathlib.Analysis.Normed.Field.ProperSpace
public import Theorem.v1.Atlas.NumberTheoryI.code.ProductFormula

@[expose] public section

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
