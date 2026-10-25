/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part2


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

def firstHitFamilyCode
    {start : Int × Int} {level : Int} {walkLength : Nat}
    {target : Int × Int}
    (w : FirstHitFamily start level walkLength target) :
    {bits : List (Bool × Bool) // bits.length = walkLength} :=
  ⟨encodePath w.1.steps, by
    simp [encodePath, w.2.2.2.1]⟩

end IsingDiagonalWalkHitSplit
end StatMech.Universality
