/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/IncreasingEvent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent


namespace StatMech

open ConfigSpace

variable {E : Type*}


def FKGLatticeCondition (π : ConfigSpace E → ℝ) : Prop :=
  ∀ ω ω', π ω * π ω' ≤ π (ω ⊔ ω') * π (ω ⊓ ω')


end StatMech
