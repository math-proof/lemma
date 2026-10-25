/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part11


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourToggleVerticalColumn_iceRule
    (omega : SixVertexArrows sixVertexFourByFourTorus)
    (column : Fin 4) (value : Bool)
    (hcolumn : forall y, omega.vertical (column, y) = value)
    (hice : omega.IceRule) :
    (sixVertexFourByFourToggleVerticalColumn column omega).IceRule := by
  intro v
  rcases v with ⟨x, y⟩
  by_cases hx : x = column
  · subst x
    simpa [sixVertexFourByFourToggleVerticalColumn,
      SixVertexArrows.incomingCount, hcolumn,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using hice (column, y)
  · simpa [sixVertexFourByFourToggleVerticalColumn,
      SixVertexArrows.incomingCount, hx]
      using hice (x, y)

theorem sixVertexFourByFourToggleVerticalColumn_upCount_false
    (omega : SixVertexArrows sixVertexFourByFourTorus)
    (column y : Fin 4)
    (hcolumn : omega.vertical (column, y) = false) :
    sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourToggleVerticalColumn column omega) y) =
      sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus omega y) + 1 := by
  rw [← sum_bool_toNat_eq_sixVertexUpCount,
    ← sum_bool_toNat_eq_sixVertexUpCount]
  change (∑ x : Fin 4,
      ((sixVertexFourByFourToggleVerticalColumn column omega).vertical
        (x, y)).toNat) =
    (∑ x : Fin 4, (omega.vertical (x, y)).toNat) + 1
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  fin_cases column <;>
    simp at hcolumn <;>
    simp [sixVertexFourByFourToggleVerticalColumn, hcolumn] <;>
    omega

theorem sixVertexFourByFourToggleVerticalColumn_upCount_true
    (omega : SixVertexArrows sixVertexFourByFourTorus)
    (column y : Fin 4)
    (hcolumn : omega.vertical (column, y) = true) :
    sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus omega y) =
      sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourToggleVerticalColumn column omega) y) + 1 := by
  rw [← sum_bool_toNat_eq_sixVertexUpCount,
    ← sum_bool_toNat_eq_sixVertexUpCount]
  change (∑ x : Fin 4, (omega.vertical (x, y)).toNat) =
    (∑ x : Fin 4,
      ((sixVertexFourByFourToggleVerticalColumn column omega).vertical
        (x, y)).toNat) + 1
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  fin_cases column <;>
    simp at hcolumn <;>
    simp [sixVertexFourByFourToggleVerticalColumn, hcolumn] <;>
    omega

theorem sixVertexFourByFourTogglePair_fineRelated
    (first second : SixVertexArrows sixVertexFourByFourTorus)
    (firstColumn secondColumn : Fin 4)
    (hfirst : forall y, first.vertical (firstColumn, y) = false)
    (hsecond : forall y, second.vertical (secondColumn, y) = true) :
    sixVertexPairAtMostTwoCycleFineRelated
      (first, second)
      (sixVertexFourByFourToggleVerticalColumn firstColumn first,
        sixVertexFourByFourToggleVerticalColumn secondColumn second) := by
  constructor
  · by_cases hcolumns : firstColumn = secondColumn
    · subst secondColumn
      apply sixVertexPairAtMostTwoCycleRelated_of_union_eq
      · funext v
        rfl
      · funext v
        rcases v with ⟨x, y⟩
        by_cases hx : x = firstColumn
        · subst x
          simp [sixVertexPairUnionVertical,
            sixVertexFourByFourToggleVerticalColumn,
            hfirst, hsecond]
        ·
          simp [sixVertexPairUnionVertical,
            sixVertexFourByFourToggleVerticalColumn, hx]
    · let family := sixVertexFourByFourOppositeVerticalColumnFamily
          firstColumn secondColumn hcolumns
      refine ⟨family, true, ?_, ?_⟩
      · funext v
        rw [show family.horizontalFlow v = 0 by
          exact sixVertexFourByFourOppositeVerticalColumnFamily_horizontalFlow
            firstColumn secondColumn hcolumns v]
        simp [sixVertexPairUnionHorizontalDelta,
          sixVertexPairUnionHorizontal,
          sixVertexFourByFourToggleVerticalColumn]
      · funext v
        rcases v with ⟨x, y⟩
        rw [show family.verticalFlow (x, y) =
            (if x = firstColumn then 1
              else if x = secondColumn then -1 else 0) by
          exact sixVertexFourByFourOppositeVerticalColumnFamily_verticalFlow
            firstColumn secondColumn hcolumns x y]
        have hcolumnsSymm : secondColumn ≠ firstColumn := Ne.symm hcolumns
        by_cases hxFirst : x = firstColumn
        · subst x
          simp only [sixVertexPairUnionVerticalDelta,
            sixVertexPairUnionVertical,
            sixVertexFourByFourToggleVerticalColumn]
          simp only [ite_true]
          split <;> simp_all
        · by_cases hxSecond : x = secondColumn
          · subst x
            simp only [sixVertexPairUnionVerticalDelta,
              sixVertexPairUnionVertical,
              sixVertexFourByFourToggleVerticalColumn]
            simp only [ite_true]
            split <;> simp_all
          · simp only [sixVertexPairUnionVerticalDelta,
              sixVertexPairUnionVertical,
              sixVertexFourByFourToggleVerticalColumn]
            simp [hxFirst, hxSecond]
  · rfl

end
end StatMech.FrontierD
