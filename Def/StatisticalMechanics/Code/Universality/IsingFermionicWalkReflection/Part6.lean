/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part4


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}

def reflectedEndpoint (level : Int) (target : Int × Int) : Int × Int :=
  (2 * level - target.1, target.2)

end IsingDiagonalWalkHitSplit
end StatMech.Universality
