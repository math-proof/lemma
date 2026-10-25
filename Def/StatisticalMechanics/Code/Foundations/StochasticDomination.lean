/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StochasticDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
open MeasureTheory


namespace StatMech

variable {E : Type*}


def StochasticallyDominated (μ ν : Measure (ConfigSpace E)) : Prop :=
  ∀ A : Set (ConfigSpace E), MeasurableSet A → IsIncreasing A → μ.real A ≤ ν.real A

end StatMech
