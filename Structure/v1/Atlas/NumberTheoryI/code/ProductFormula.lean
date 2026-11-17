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


public noncomputable section

open MeasureTheory Measure TopologicalSpace Pointwise Filter Topology

structure IsRadonMeasure {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X]
    (μ : MeasureTheory.Measure X) : Prop where
  isFiniteMeasureOnCompacts : MeasureTheory.IsFiniteMeasureOnCompacts μ
  regular : MeasureTheory.Measure.Regular μ
  innerRegular : MeasureTheory.Measure.InnerRegular μ

end
