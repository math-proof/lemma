/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part8


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredSlotIntPosition_injective (n : Nat) :
    Function.Injective (fkIsingSquareWiredSlotIntPosition n) := by
  rintro ⟨u, i⟩ ⟨v, j⟩ h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases i <;> fin_cases j <;>
    simp [fkIsingSquareWiredSlotIntPosition,
      fkIsingSquareWiredPortOctagonOffset] at hx hy
  all_goals try omega
  all_goals
    have h0 : u.1 0 = v.1 0 := by omega
    have h1 : u.1 1 = v.1 1 := by omega
    have huv : u = v := by
      apply Subtype.ext
      funext k
      fin_cases k
      · exact h0
      · exact h1
    subst v
    rfl


end
end StatMech.Universality
