/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ProductMeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Foundations.ProductMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace StatMech

variable {E : Type*}


instance (p : ℝ≥0) (hp : p ≤ 1) : IsProbabilityMeasure (bernoulliMeasure p hp) := by
  unfold bernoulliMeasure; infer_instance


end StatMech
