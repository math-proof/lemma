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
public import Structure.v1.Atlas.NumberTheoryI.code.ProductFormula

@[expose] public section

noncomputable section

open MeasureTheory Measure TopologicalSpace Pointwise Filter Topology

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

end
