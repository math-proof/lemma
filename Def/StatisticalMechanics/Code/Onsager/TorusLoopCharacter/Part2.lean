/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopCharacter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.SpinCharacter.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TorusContractibleLoop
import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopCharacter


namespace StatMech.Onsager

open Matrix BigOperators

def ons_spinLinearCharacter (a b : Fin 2) (h : Fin 2 × Fin 2) : ℂ :=
  (-1 : ℂ) ^ (a.val * h.1.val + b.val * h.2.val)

end StatMech.Onsager
