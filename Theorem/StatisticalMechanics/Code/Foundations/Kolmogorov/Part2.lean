/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kolmogorov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Instance.StatisticalMechanics.Code.Foundations.Kolmogorov.Part2
open MeasureTheory


namespace StatMech

namespace Kolmogorov

variable {E : Type*} (μ : E → Measure Bool) [∀ e, IsProbabilityMeasure (μ e)]


theorem configExtension_isProjectiveLimit :
    IsProjectiveLimit (configExtension μ)
      (fun I : Finset E => Measure.pi (fun e : I => μ e)) :=
  extension_isProjectiveLimit μ


theorem configExtension_unique {ν : Measure (ConfigSpace E)}
    (hν : ∀ (s : Finset E) (t : E → Set Bool),
      (∀ e, MeasurableSet (t e)) → ν (Set.pi s t) = ∏ e ∈ s, μ e (t e)) :
    ν = configExtension μ :=
  extension_unique μ hν

end Kolmogorov
end StatMech
