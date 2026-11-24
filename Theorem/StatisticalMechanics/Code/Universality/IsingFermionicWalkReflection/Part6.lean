module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}

theorem natCard_firstHitFamily_eq_reflected
    (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Nat.card (FirstHitFamily start level walkLength target) =
      Nat.card (FirstHitFamily start level walkLength
        (reflectedEndpoint level target)) :=
  Nat.card_congr (reflectFirstHitFamilyEquiv start level walkLength target)


end IsingDiagonalWalkHitSplit
end StatMech.Universality
