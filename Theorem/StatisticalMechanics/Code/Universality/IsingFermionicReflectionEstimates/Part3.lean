/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part4


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

theorem firstHitFamilyCode_injective
    {start : Int × Int} {level : Int} {walkLength : Nat}
    {target : Int × Int} :
    Function.Injective (@firstHitFamilyCode start level walkLength target) := by
  intro w v h
  have hcode : encodePath w.1.steps = encodePath v.1.steps :=
    congrArg Subtype.val h
  have hsteps := encodePath_injective_of_valid w.2.2.1 v.2.2.1 hcode
  have hw := firstHitSplit_eq_some w.1 w.2.1
  have hv := firstHitSplit_eq_some v.1 v.2.1
  have hwv : w.1 = v.1 := by
    apply Option.some.inj
    rw [← hw, ← hv, hsteps]
  exact Subtype.ext hwv

end IsingDiagonalWalkHitSplit
end StatMech.Universality
