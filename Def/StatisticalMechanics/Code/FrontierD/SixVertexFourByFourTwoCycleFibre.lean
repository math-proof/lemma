/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourVertex (x y : Nat) :
    sixVertexFourByFourTorus.Vertex :=
  (⟨x % 4, Nat.mod_lt _ (by norm_num)⟩,
    ⟨y % 4, Nat.mod_lt _ (by norm_num)⟩)

def sixVertexFourByFourArrowsOfMasks
    (horizontalMask verticalMask : Nat) :
    SixVertexArrows sixVertexFourByFourTorus where
  horizontal v := horizontalMask.testBit (v.2.val * 4 + v.1.val)
  vertical v := verticalMask.testBit (v.2.val * 4 + v.1.val)

def sixVertexFourByFourReverseRow : Fin 4 -> Fin 4 := ![0, 3, 2, 1]


def sixVertexFourByFourVerticalColumnCycle
    (x : Fin 4) (positive : Bool) :
    SixVertexDirectedSimpleCycle sixVertexFourByFourTorus where
  length := 4
  length_pos := by norm_num
  edge i := if positive then
      .vertical (x, i) true
    else
      .vertical (x, sixVertexFourByFourReverseRow i) false
  head_eq_next_tail := by
    intro i
    fin_cases positive <;> fin_cases i <;>
      apply Prod.ext <;> apply Fin.ext <;>
      norm_num [SixVertexDirectedTorusEdge.head,
          SixVertexDirectedTorusEdge.tail,
          sixVertexFourByFourReverseRow, finitePeriodicSucc,
          sixVertexFourByFourTorus]
  tail_injective := by
    intro i j hij
    fin_cases positive <;> fin_cases i <;> fin_cases j <;>
      simp_all [SixVertexDirectedTorusEdge.tail,
        sixVertexFourByFourReverseRow, finitePeriodicSucc,
        sixVertexFourByFourTorus]
  physical_injective := by
    intro i j hij
    fin_cases positive <;> fin_cases i <;> fin_cases j <;>
      simp_all [SixVertexDirectedTorusEdge.physical,
        sixVertexFourByFourReverseRow]


def sixVertexFourByFourOppositeVerticalColumnFamily
    (positiveColumn negativeColumn : Fin 4)
    (hne : positiveColumn ≠ negativeColumn) :
    SixVertexAtMostTwoCycleFamily sixVertexFourByFourTorus where
  count := 2
  count_le_two := by norm_num
  cycle i := if i = 0 then
      sixVertexFourByFourVerticalColumnCycle positiveColumn true
    else
      sixVertexFourByFourVerticalColumnCycle negativeColumn false
  tail_disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · simp at hij
    · intro a b
      simp [sixVertexFourByFourVerticalColumnCycle,
        SixVertexDirectedTorusEdge.tail,
        sixVertexFourByFourReverseRow]
      intro hcolumns
      exact (hne hcolumns).elim
    · intro a b
      simp [sixVertexFourByFourVerticalColumnCycle,
        SixVertexDirectedTorusEdge.tail,
        sixVertexFourByFourReverseRow]
      intro hcolumns
      exact (hne hcolumns.symm).elim
    · simp at hij

end
end StatMech.FrontierD
