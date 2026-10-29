/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InhomogeneousProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InfiniteBK
import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


namespace StatMech

variable {E : Type*}


noncomputable def inhomBernoulliProductMeasure (p : E → NNReal)
    (hp : ∀ e, p e ≤ 1) : Measure (ConfigSpace E) :=
  Measure.infinitePi (fun e => bernoulliMeasure (p e) (hp e))

end StatMech
