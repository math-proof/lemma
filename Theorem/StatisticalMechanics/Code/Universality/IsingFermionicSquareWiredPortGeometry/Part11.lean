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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part11


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredExpandedIntPosition_injective
    (n : Nat) (hn : 0 < n) :
    Function.Injective (fkIsingSquareWiredExpandedIntPosition n hn) := by
  intro x y h
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          exact congrArg Sum.inl
            (fkIsingSquareWiredSlotIntPosition_injective n h)
      | inr k =>
          exfalso
          rcases x with ⟨u, i⟩
          have hx := congrArg Prod.fst h
          have hy := congrArg Prod.snd h
          have ub0 := fkIsingSquareVertex_coordinate_bounds n u 0
          fin_cases i <;>
            simp [fkIsingSquareWiredExpandedIntPosition,
              fkIsingSquareWiredSlotIntPosition,
              fkIsingSquareWiredPortOctagonOffset,
              fkIsingSquareLeftVerticalLower] at hx hy <;> omega
  | inr k =>
      cases y with
      | inl y =>
          exfalso
          rcases y with ⟨u, i⟩
          have hx := congrArg Prod.fst h
          have hy := congrArg Prod.snd h
          have ub0 := fkIsingSquareVertex_coordinate_bounds n u 0
          fin_cases i <;>
            simp [fkIsingSquareWiredExpandedIntPosition,
              fkIsingSquareWiredSlotIntPosition,
              fkIsingSquareWiredPortOctagonOffset,
              fkIsingSquareLeftVerticalLower] at hx hy <;> omega
      | inr l =>
          apply congrArg Sum.inr
          apply Fin.ext
          have hy := congrArg Prod.snd h
          simp [fkIsingSquareWiredExpandedIntPosition,
            fkIsingSquareLeftVerticalLower] at hy
          omega

end
end StatMech.Universality
