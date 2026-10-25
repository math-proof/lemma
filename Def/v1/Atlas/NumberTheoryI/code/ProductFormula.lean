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
import Structure.v1.Atlas.NumberTheoryI.code.ProductFormula


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
