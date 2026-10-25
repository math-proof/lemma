/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part14


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}


theorem natCard_firstHitFamily_eq_mirroredStart
    (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Nat.card (FirstHitFamily start level walkLength target) =
      Nat.card (FirstHitFamily (reflectedEndpoint level start) level
        walkLength target) :=
  Nat.card_congr
    (reflectPrefixFirstHitFamilyEquiv start level walkLength target)


end IsingDiagonalWalkHitSplit
end StatMech.Universality
