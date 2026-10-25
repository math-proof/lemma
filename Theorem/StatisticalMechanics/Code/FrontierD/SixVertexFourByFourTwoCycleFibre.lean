/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourOppositeVerticalColumnFamily_horizontalFlow
    (firstColumn secondColumn : Fin 4) (hne : firstColumn ≠ secondColumn)
    (v : sixVertexFourByFourTorus.Vertex) :
    (sixVertexFourByFourOppositeVerticalColumnFamily
      firstColumn secondColumn hne).horizontalFlow v = 0 := by
  rcases v with ⟨x, y⟩
  unfold SixVertexAtMostTwoCycleFamily.horizontalFlow
  simp only [sixVertexFourByFourOppositeVerticalColumnFamily]
  change (∑ i : Fin 2,
      (if i = 0 then
        sixVertexFourByFourVerticalColumnCycle firstColumn true
      else sixVertexFourByFourVerticalColumnCycle secondColumn false).horizontalFlow
        (x, y)) = 0
  rw [Fin.sum_univ_two]
  simp only [if_neg (by decide : (1 : Fin 2) ≠ 0), ite_true]
  unfold SixVertexDirectedSimpleCycle.horizontalFlow
  simp only [sixVertexFourByFourVerticalColumnCycle]
  simp only [ite_true, Bool.false_eq_true, if_false]
  change (∑ i : Fin 4,
      (SixVertexDirectedTorusEdge.vertical (firstColumn, i) true).horizontalFlow
        (x, y)) +
    (∑ i : Fin 4,
      (SixVertexDirectedTorusEdge.vertical
        (secondColumn, sixVertexFourByFourReverseRow i) false).horizontalFlow
          (x, y)) = 0
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  simp [SixVertexDirectedTorusEdge.horizontalFlow]

set_option maxHeartbeats 1000000 in

theorem sixVertexFourByFourOppositeVerticalColumnFamily_verticalFlow
    (firstColumn secondColumn : Fin 4) (hne : firstColumn ≠ secondColumn)
    (x y : Fin 4) :
    (sixVertexFourByFourOppositeVerticalColumnFamily
      firstColumn secondColumn hne).verticalFlow (x, y) =
      (if x = firstColumn then 1 else if x = secondColumn then -1 else 0) := by
  unfold SixVertexAtMostTwoCycleFamily.verticalFlow
  simp only [sixVertexFourByFourOppositeVerticalColumnFamily]
  change (∑ i : Fin 2,
      (if i = 0 then
        sixVertexFourByFourVerticalColumnCycle firstColumn true
      else sixVertexFourByFourVerticalColumnCycle secondColumn false).verticalFlow
        (x, y)) = _
  rw [Fin.sum_univ_two]
  simp only [if_neg (by decide : (1 : Fin 2) ≠ 0), ite_true]
  unfold SixVertexDirectedSimpleCycle.verticalFlow
  simp only [sixVertexFourByFourVerticalColumnCycle]
  simp only [ite_true, Bool.false_eq_true, if_false]
  change (∑ i : Fin 4,
      (SixVertexDirectedTorusEdge.vertical (firstColumn, i) true).verticalFlow
        ((x, y) : sixVertexFourByFourTorus.Vertex)) +
    (∑ i : Fin 4,
      (SixVertexDirectedTorusEdge.vertical
        (secondColumn, sixVertexFourByFourReverseRow i) false).verticalFlow
          ((x, y) : sixVertexFourByFourTorus.Vertex)) = _
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  fin_cases firstColumn <;> fin_cases secondColumn <;>
    fin_cases x <;> fin_cases y <;>
    simp_all [SixVertexDirectedTorusEdge.verticalFlow,
      sixVertexFourByFourReverseRow]

end
end StatMech.FrontierD
