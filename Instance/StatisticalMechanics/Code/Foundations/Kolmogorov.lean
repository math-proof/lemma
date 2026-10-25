/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kolmogorov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Foundations.Kolmogorov
open MeasureTheory


namespace StatMech

namespace Kolmogorov

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]


instance isProbabilityMeasure : IsProbabilityMeasure (extension μ) := by
  unfold extension; infer_instance

end Kolmogorov
end StatMech
