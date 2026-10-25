/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part8


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}

theorem firstHitFamilyWeight_eq_reflected
    (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    firstHitFamilyWeight start level walkLength target =
      firstHitFamilyWeight start level walkLength
        (reflectedEndpoint level target) := by
  unfold firstHitFamilyWeight
  rw [natCard_firstHitFamily_eq_reflected]


theorem firstHitSplit_reflect {path : List (Int × Int)}
    {w : IsingDiagonalWalkHitSplit start level}
    (h : isingDiagonalWalkFirstHitSplit? start level path = some w) :
    isingDiagonalWalkFirstHitSplit? start level w.reflect.steps =
      some w.reflect :=
  firstHitSplit_eq_some w.reflect (reflect_firstHit w
    (firstHitSplit_firstHit h))

end IsingDiagonalWalkHitSplit
end StatMech.Universality
