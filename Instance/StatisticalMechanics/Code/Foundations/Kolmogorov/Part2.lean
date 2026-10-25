/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kolmogorov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Foundations.Kolmogorov.Part2
open MeasureTheory


namespace StatMech

namespace Kolmogorov

variable {E : Type*} (μ : E → Measure Bool) [∀ e, IsProbabilityMeasure (μ e)]


instance : IsProbabilityMeasure (configExtension μ) := by
  unfold configExtension; infer_instance


end Kolmogorov
end StatMech
