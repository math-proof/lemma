/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ProductMeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Instance.StatisticalMechanics.Code.Foundations.ProductMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace StatMech

variable {E : Type*}


@[simp] lemma bernoulliMeasure_apply_true (p : ℝ≥0) (hp : p ≤ 1) :
    bernoulliMeasure p hp {true} = (p : ℝ≥0∞) := by
  unfold bernoulliMeasure
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.bernoulli_apply]
  rfl


@[simp] lemma bernoulliMeasure_apply_false (p : ℝ≥0) (hp : p ≤ 1) :
    bernoulliMeasure p hp {false} = ((1 - p : ℝ≥0) : ℝ≥0∞) := by
  unfold bernoulliMeasure
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.bernoulli_apply]
  rfl


end StatMech
