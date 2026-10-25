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
import Def.v1.Atlas.NumberTheoryI.code.ProductFormula.Part2


noncomputable section

open MeasureTheory Measure TopologicalSpace Pointwise Filter Topology

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

end
