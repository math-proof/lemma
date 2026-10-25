/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part6


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}

noncomputable def firstHitFamilyWeight
    (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) : Real :=
  Nat.card (FirstHitFamily start level walkLength target) /
    4 ^ walkLength


end IsingDiagonalWalkHitSplit
end StatMech.Universality
