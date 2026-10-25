/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleExponent.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalCoefficient.Part2


namespace StatMech.Onsager

open BigOperators Finset SimpleGraph StatMech.Ising

def ons_IsSquarefreeExponent {E : Type*} (m : E →₀ ℕ) : Prop :=
  ∀ edge, m edge ≤ 1

end StatMech.Onsager
