/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kolmogorov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Foundations.Kolmogorov

@[expose] public section

open MeasureTheory


namespace StatMech

namespace Kolmogorov

variable {E : Type*} (μ : E → Measure Bool) [∀ e, IsProbabilityMeasure (μ e)]


noncomputable def configExtension : Measure (ConfigSpace E) := extension μ


end Kolmogorov
end StatMech
