/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part11
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourTorus : EvenTorus where
  width := 4
  height := 4
  width_pos := by norm_num
  height_pos := by norm_num
  width_even := by norm_num
  height_even := by norm_num

def sixVertexFourByFourSectorZero : Fin 5 := ⟨0, by norm_num⟩

def sixVertexFourByFourSectorOne : Fin 5 := ⟨1, by norm_num⟩

def sixVertexFourByFourSectorTwo : Fin 5 := ⟨2, by norm_num⟩

def sixVertexFourByFourSectorThree : Fin 5 := ⟨3, by norm_num⟩

def piFinFourEquiv (A : Type*) : (Fin 4 → A) ≃ A × A × A × A where
  toFun f := (f 0, f 1, f 2, f 3)
  invFun rows := ![rows.1, rows.2.1, rows.2.2.1, rows.2.2.2]
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv rows := by
    rcases rows with ⟨row0, row1, row2, row3⟩
    rfl

def sixVertexHorizontalTransitionCountExecutable
    {T : EvenTorus} (previous current : SixVertexRow T.width) : Nat :=
  ((Finset.univ : Finset (SixVertexRow T.width)).filter fun horizontal =>
    svHorizontalIce T.width_pos
      previous current horizontal).card

def sixVertexHorizontalTransitionWitnessCountExecutable
    {T : EvenTorus} (vertical : Fin T.height → SixVertexRow T.width)
    (j : Fin T.height) : Nat :=
  sixVertexHorizontalTransitionCountExecutable
    (T := T) (vertical (SixVertexArrows.cyclicPred T.height_pos j))
      (vertical j)

def sixVertexFourRowOfIndex (index : Fin 16) : SixVertexRow 4 := fun i =>
  Nat.testBit index.val i.val

end
end StatMech.FrontierD
