/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/IncreasingEvent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2


namespace StatMech

open ConfigSpace

variable {E : Type*}


lemma FKGLatticeCondition.of_logModular {π : ConfigSpace E → ℝ}
    (h : ∀ ω ω', π ω * π ω' = π (ω ⊔ ω') * π (ω ⊓ ω')) : FKGLatticeCondition π :=
  fun ω ω' => le_of_eq (h ω ω')

end StatMech
