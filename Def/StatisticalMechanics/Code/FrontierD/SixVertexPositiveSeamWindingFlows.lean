/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamWindingFlows.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWindingCycleBranchRecovery.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexPositiveVerticalWindingCycle {T : EvenTorus}
    (column : Fin T.width) : SixVertexDirectedSimpleCycle T where
  length := T.height
  length_pos := T.height_pos
  edge := fun row => .vertical (column, row) true
  head_eq_next_tail := by
    intro row
    rfl
  tail_injective := by
    intro first second h
    exact congrArg Prod.snd h
  physical_injective := by
    intro first second h
    exact congrArg (fun edge => edge.2.2) h


def sixVertexPositiveHorizontalWindingCycle {T : EvenTorus}
    (row : Fin T.height) : SixVertexDirectedSimpleCycle T where
  length := T.width
  length_pos := T.width_pos
  edge := fun column => .horizontal (column, row) true
  head_eq_next_tail := by
    intro column
    rfl
  tail_injective := by
    intro first second h
    exact congrArg Prod.fst h
  physical_injective := by
    intro first second h
    exact congrArg (fun edge => edge.2.1) h


def SixVertexAtMostTwoCycleFamily.single {T : EvenTorus}
    (cycle : SixVertexDirectedSimpleCycle T) :
    SixVertexAtMostTwoCycleFamily T where
  count := 1
  count_le_two := by omega
  cycle := fun _ => cycle
  tail_disjoint := by
    intro i j hne
    fin_cases i
    fin_cases j
    simp at hne


def sixVertexPositiveVerticalWindingFamily {T : EvenTorus}
    (column : Fin T.width) : SixVertexAtMostTwoCycleFamily T :=
  .single (sixVertexPositiveVerticalWindingCycle column)


def sixVertexPositiveHorizontalWindingFamily {T : EvenTorus}
    (row : Fin T.height) : SixVertexAtMostTwoCycleFamily T :=
  .single (sixVertexPositiveHorizontalWindingCycle row)

end
end StatMech.FrontierD
