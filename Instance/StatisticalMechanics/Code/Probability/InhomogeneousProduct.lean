/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InhomogeneousProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InfiniteBK
import Def.StatisticalMechanics.Code.Probability.InhomogeneousProduct
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


namespace StatMech

variable {E : Type*}


instance (p : E → NNReal) (hp : ∀ e, p e ≤ 1) :
    IsProbabilityMeasure (inhomBernoulliProductMeasure p hp) := by
  unfold inhomBernoulliProductMeasure
  infer_instance

end StatMech
