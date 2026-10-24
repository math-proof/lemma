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

noncomputable section

open MeasureTheory Measure TopologicalSpace Pointwise Filter Topology

structure IsRadonMeasure {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X]
    (μ : MeasureTheory.Measure X) : Prop where
  isFiniteMeasureOnCompacts : MeasureTheory.IsFiniteMeasureOnCompacts μ
  regular : MeasureTheory.Measure.Regular μ
  innerRegular : MeasureTheory.Measure.InnerRegular μ

def mulLeftContinuousAddEquiv {K : Type*} [NormedField K]
    {a : K} (ha : a ≠ 0) : K ≃ₜ+ K :=
  ContinuousAddEquiv.mk
    { toFun := (a * ·)
      invFun := (a⁻¹ * ·)
      left_inv := fun x => by
        show a⁻¹ * (a * x) = x; rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      right_inv := fun x => by
        show a * (a⁻¹ * x) = x; rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
      map_add' := fun x y => by show a * (x + y) = a * x + a * y; ring }

@[simp] lemma mulLeftContinuousAddEquiv_apply {K : Type*} [NormedField K]
    {a : K} (ha : a ≠ 0) (x : K) :
    mulLeftContinuousAddEquiv ha x = a * x := rfl

open MeasureTheory MeasureTheory.Measure Metric Pointwise in
def IsNormalizedAbsVal
    {K : Type*} [Field K] [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [LocallyCompactSpace K] [T2Space K]
    (f : K → ℝ) : Prop :=
  (∀ a, 0 ≤ f a) ∧
  ∀ (μ : Measure K) [μ.IsAddHaarMeasure] (a : K) (S : Set K),
    μ ((a * ·) '' S) = ENNReal.ofReal (f a) * μ S

class IsGlobalField (K : Type*) [Field K] where
  PlaceType : Type*
  place_nonempty : Nonempty PlaceType
  Completion : PlaceType → Type*
  completionField : ∀ v, Field (Completion v)
  completionTopologicalSpace : ∀ v, TopologicalSpace (Completion v)
  completionLocallyCompact : ∀ v,
    @LocallyCompactSpace (Completion v) (completionTopologicalSpace v)
  completionNontrivial : ∀ v, @Nontrivial (Completion v)
  absVal : PlaceType → AbsoluteValue K ℝ
  exponent : PlaceType → ℝ
  exponent_pos : ∀ v, 0 < exponent v
  normAbsVal : PlaceType → K → ℝ
  normAbsVal_nonneg : ∀ v x, 0 ≤ normAbsVal v x
  normAbsVal_eq : ∀ v x, normAbsVal v x = (absVal v x) ^ (exponent v)
  normAbsVal_eq_one_of_finite : ∀ x, x ≠ 0 →
    Set.Finite {v | normAbsVal v x ≠ 1}
  product_formula : ∀ x, x ≠ 0 → ∏ᶠ v, normAbsVal v x = 1
