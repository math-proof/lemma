/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowBlockRepetition.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part3
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectOrientedEvenRowBlockOfReflectedCarrier_carrier
    (R : FKRectTorus) (q : Real) (scale : Nat)
    (S : Set R.Vertex) (x y : S)
    (hspan : (scale : Int) ≤
      2 * |(y.1.2.val : Int) - x.1.2.val| + 2)
    (hrows : x.1.2.val ≤ 8 * scale + 1 ∧
      y.1.2.val ≤ 8 * scale + 1)
    {massFloor : Real} (hmassFloor : 0 ≤ massFloor)
    (hlower : massFloor ≤
      fkRectCriticalEventMass R q
        (fkRectReflectedCarrierConnectionEvent R S x y))
    (hcolumns : ∀ v ∈
      S ∪ fkRectDevelopedReflectionSet R y.1.2.val S,
      v.1.val ≤ 4 * scale) :
    (fkRectOrientedEvenRowBlockOfReflectedCarrier
      R q scale S x y hspan hrows hmassFloor hlower hcolumns).carrier =
        S ∪ fkRectDevelopedReflectionSet R y.1.2.val S := by
  by_cases hxy : x.1.2.val ≤ y.1.2.val <;>
    simp [fkRectOrientedEvenRowBlockOfReflectedCarrier, hxy]

@[simp] theorem fkRectOrientedEvenRowBlockOfReflectedCarrier_massFloor
    (R : FKRectTorus) (q : Real) (scale : Nat)
    (S : Set R.Vertex) (x y : S)
    (hspan : (scale : Int) ≤
      2 * |(y.1.2.val : Int) - x.1.2.val| + 2)
    (hrows : x.1.2.val ≤ 8 * scale + 1 ∧
      y.1.2.val ≤ 8 * scale + 1)
    {massFloor : Real} (hmassFloor : 0 ≤ massFloor)
    (hlower : massFloor ≤
      fkRectCriticalEventMass R q
        (fkRectReflectedCarrierConnectionEvent R S x y))
    (hcolumns : ∀ v ∈
      S ∪ fkRectDevelopedReflectionSet R y.1.2.val S,
      v.1.val ≤ 4 * scale) :
    (fkRectOrientedEvenRowBlockOfReflectedCarrier
      R q scale S x y hspan hrows hmassFloor hlower hcolumns).massFloor =
        massFloor := by
  by_cases hxy : x.1.2.val ≤ y.1.2.val <;>
    simp [fkRectOrientedEvenRowBlockOfReflectedCarrier, hxy]


theorem fkRectQuarterTurn_developedThreeByOneCarrier_row_bounds
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (hH : 4 < R.height)
    {v : (fkRectQuarterTurnTorus R hH).Vertex}
    (hv : v ∈ fkRectQuarterTurnSet R hH
      (fkRectDevelopedThreeByOneTorusCarrier R n)) :
    v.2.val ≤ 8 * n + 1 := by
  rcases hv with ⟨w, hw, rfl⟩
  rw [fkRectQuarterTurnVertexEquiv_apply,
    fkRectQuarterTurnVertex_snd_val]
  have hwcol := fkRectDevelopedThreeByOneTorusCarrier_column_bounds
    R n hn hwidth hheight hw
  have hwmod := Nat.mod_lt w.2.val (by norm_num : 0 < 2)
  omega

theorem fkRectDevelopedThreeByOne_reflectedUnion_evenOffset_row_bounds
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 12 * n + 2 < R.height)
    (center : Nat) (hcenter : center ≤ 4 * n)
    {v : R.Vertex}
    (hv : v ∈ fkRectEvenRowTranslationSet R (4 * n + 2)
      (fkRectDevelopedThreeByOneTorusCarrier R n ∪
        fkRectDevelopedReflectionSet R center
          (fkRectDevelopedThreeByOneTorusCarrier R n))) :
    1 ≤ v.2.val ∧ v.2.val ≤ 12 * n + 2 := by
  rcases hv with ⟨w, hw, rfl⟩
  rw [fkRectEvenRowTranslationVertexEquiv_apply]
  rcases hw with hw | hw
  · have hwrow := fkRectDevelopedThreeByOneTorusCarrier_row_bounds
      R n hwidth (by omega) hw
    rw [fkRectRowTranslate_eq_add_of_lt R (4 * n + 2) w.2 (by omega)]
    simp only [Fin.val_mk]
    omega
  · rcases hw with ⟨z, hz, rfl⟩
    have hzrow := fkRectDevelopedThreeByOneTorusCarrier_row_bounds
      R n hwidth (by omega) hz
    rw [fkRectDevelopedReflectionVertexEquiv_apply,
      fkRectRowTranslate_reflection_eq_sub R (4 * n + 2) center z.2
        (by omega) (by omega)]
    simp only [Fin.val_mk]
    omega

theorem fkRectQuarterTurn_reflectedUnion_evenOffset_row_bounds
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (hH : 4 < R.height)
    (hrotHeight : 24 * n + 4 <
      (fkRectQuarterTurnTorus R hH).height)
    (center : Nat) (hcenter : center ≤ 8 * n + 1)
    {v : (fkRectQuarterTurnTorus R hH).Vertex}
    (hv : v ∈ fkRectEvenRowTranslationSet
      (fkRectQuarterTurnTorus R hH) (8 * n + 2)
      (fkRectQuarterTurnSet R hH
          (fkRectDevelopedThreeByOneTorusCarrier R n) ∪
        fkRectDevelopedReflectionSet
          (fkRectQuarterTurnTorus R hH) center
          (fkRectQuarterTurnSet R hH
            (fkRectDevelopedThreeByOneTorusCarrier R n)))) :
    1 ≤ v.2.val ∧ v.2.val ≤ 24 * n + 4 := by
  rcases hv with ⟨w, hw, rfl⟩
  rw [fkRectEvenRowTranslationVertexEquiv_apply]
  rcases hw with hw | hw
  · have hwrow := fkRectQuarterTurn_developedThreeByOneCarrier_row_bounds
      R n hn hwidth hheight hH hw
    rw [fkRectRowTranslate_eq_add_of_lt
      (fkRectQuarterTurnTorus R hH) (8 * n + 2) w.2 (by omega)]
    simp only [Fin.val_mk]
    omega
  · rcases hw with ⟨z, hz, rfl⟩
    have hzrow := fkRectQuarterTurn_developedThreeByOneCarrier_row_bounds
      R n hn hwidth hheight hH hz
    rw [fkRectDevelopedReflectionVertexEquiv_apply,
      fkRectRowTranslate_reflection_eq_sub
        (fkRectQuarterTurnTorus R hH) (8 * n + 2) center z.2
        (by omega) (by omega)]
    simp only [Fin.val_mk]
    omega


theorem fkRectCritical_developedThreeByOne_exists_orientedEvenRowBlock
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    let hH : 4 < R.height := by omega
    Nonempty (FKRectOrientedEvenRowBlock R q n) ∨
      Nonempty (FKRectOrientedEvenRowBlock
        (fkRectQuarterTurnTorus R hH) q n) := by
  dsimp only
  let hH : 4 < R.height := by omega
  obtain ⟨p, hp, haxis⟩ :=
    fkRectCritical_developedThreeByOne_exists_axisSelectedWindingBlock_ge
      R n hn hwidth hheight hq
  let S := fkRectDevelopedThreeByOneTorusCarrier R n
  let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1
  let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2
  rcases haxis with horiginal | hturned
  · left
    constructor
    apply fkRectOrientedEvenRowBlockOfReflectedCarrier
      R q n S x y
    · have hrow : (n : Int) ≤
          2 * |(y.1.2.val : Int) - x.1.2.val| := by
        simpa [x, y] using horiginal.1
      exact hrow.trans (by omega)
    · constructor
      · exact (fkRectDevelopedThreeByOneTorusCarrier_row_bounds
          R n hwidth hheight x.2).trans (by omega)
      · exact (fkRectDevelopedThreeByOneTorusCarrier_row_bounds
          R n hwidth hheight y.2).trans (by omega)
    · exact (fkRectDevelopedReflectedEndpointLower_pos hq n).le
    · exact horiginal.2
    · intro v hv
      exact (fkRectDevelopedThreeByOne_reflectedUnion_column_bounds
        R n hn hwidth hheight y.1.2.val hv).2
  · right
    constructor
    let ST := fkRectQuarterTurnSet R hH S
    let xT : ST := fkRectQuarterTurnSetEquiv R hH S x
    let yT : ST := fkRectQuarterTurnSetEquiv R hH S y
    apply fkRectOrientedEvenRowBlockOfReflectedCarrier
      (fkRectQuarterTurnTorus R hH) q n ST xT yT
    · exact hturned.1
    · constructor
      · exact fkRectQuarterTurn_developedThreeByOneCarrier_row_bounds
          R n hn hwidth hheight hH xT.2
      · exact fkRectQuarterTurn_developedThreeByOneCarrier_row_bounds
          R n hn hwidth hheight hH yT.2
    · exact (fkRectDevelopedReflectedEndpointLower_pos hq n).le
    · exact hturned.2
    · intro v hv
      exact (fkRectQuarterTurn_developedThreeByOne_reflectedUnion_column_bounds
        R n hwidth hheight hH yT.1.2.val hv).trans (by omega)


theorem fkRectCritical_developedThreeByOne_exists_positiveRowOrientedBlock
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 12 * n + 2 < R.width)
    (hheight : 12 * n + 2 < R.height)
    {q : Real} (hq : 1 ≤ q) :
    let hH : 4 < R.height := by omega
    Nonempty (FKRectPositiveRowOrientedBlock R q n) ∨
      Nonempty (FKRectPositiveRowOrientedBlock
        (fkRectQuarterTurnTorus R hH) q n) := by
  dsimp only
  let hH : 4 < R.height := by omega
  have hwidth' : 4 * n < R.width := by omega
  have hheight' : 4 * n < R.height := by omega
  obtain ⟨p, hp, haxis⟩ :=
    fkRectCritical_developedThreeByOne_exists_axisSelectedWindingBlock_ge
      R n hn hwidth' hheight' hq
  let S := fkRectDevelopedThreeByOneTorusCarrier R n
  let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1
  let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2
  rcases haxis with horiginal | hturned
  · left
    have hspan : (n : Int) ≤
        2 * |(y.1.2.val : Int) - x.1.2.val| + 2 := by
      have hspan' : (n : Int) ≤
          2 * |(y.1.2.val : Int) - x.1.2.val| := by
        simpa [x, y] using horiginal.1
      exact hspan'.trans (by omega)
    have hrows : x.1.2.val ≤ 8 * n + 1 ∧
        y.1.2.val ≤ 8 * n + 1 := by
      constructor
      · exact (fkRectDevelopedThreeByOneTorusCarrier_row_bounds
          R n hwidth' hheight' x.2).trans (by omega)
      · exact (fkRectDevelopedThreeByOneTorusCarrier_row_bounds
          R n hwidth' hheight' y.2).trans (by omega)
    have hcolumns : ∀ v ∈
        S ∪ fkRectDevelopedReflectionSet R y.1.2.val S,
        v.1.val ≤ 4 * n := by
      intro v hv
      exact (fkRectDevelopedThreeByOne_reflectedUnion_column_bounds
        R n hn hwidth' hheight' y.1.2.val hv).2
    let B0 := fkRectOrientedEvenRowBlockOfReflectedCarrier
      R q n S x y hspan hrows
        (fkRectDevelopedReflectedEndpointLower_pos hq n).le
        horiginal.2 hcolumns
    have hoffset : Even (4 * n + 2) := by
      rw [show 4 * n + 2 = 2 * (2 * n + 1) by omega]
      exact even_two_mul _
    let B := B0.translate (4 * n + 2) hoffset
    refine ⟨⟨B, ?_⟩⟩
    intro v hv
    have hcenter : y.1.2.val ≤ 4 * n :=
      fkRectDevelopedThreeByOneTorusCarrier_row_bounds
        R n hwidth' hheight' y.2
    have hv' : v ∈ fkRectEvenRowTranslationSet R (4 * n + 2)
        (fkRectDevelopedThreeByOneTorusCarrier R n ∪
          fkRectDevelopedReflectionSet R y.1.2.val
            (fkRectDevelopedThreeByOneTorusCarrier R n)) := by
      simpa [B, B0, S] using hv
    have hb :=
      fkRectDevelopedThreeByOne_reflectedUnion_evenOffset_row_bounds
        R n hwidth' hheight y.1.2.val hcenter hv'
    exact ⟨hb.1, hb.2.trans (by omega)⟩
  · right
    let ST := fkRectQuarterTurnSet R hH S
    let xT : ST := fkRectQuarterTurnSetEquiv R hH S x
    let yT : ST := fkRectQuarterTurnSetEquiv R hH S y
    have hrows : xT.1.2.val ≤ 8 * n + 1 ∧
        yT.1.2.val ≤ 8 * n + 1 := by
      constructor
      · exact fkRectQuarterTurn_developedThreeByOneCarrier_row_bounds
          R n hn hwidth' hheight' hH xT.2
      · exact fkRectQuarterTurn_developedThreeByOneCarrier_row_bounds
          R n hn hwidth' hheight' hH yT.2
    have hcolumns : ∀ v ∈
        ST ∪ fkRectDevelopedReflectionSet
          (fkRectQuarterTurnTorus R hH) yT.1.2.val ST,
        v.1.val ≤ 4 * n := by
      intro v hv
      exact (fkRectQuarterTurn_developedThreeByOne_reflectedUnion_column_bounds
        R n hwidth' hheight' hH yT.1.2.val hv).trans (by omega)
    let B0 := fkRectOrientedEvenRowBlockOfReflectedCarrier
      (fkRectQuarterTurnTorus R hH) q n ST xT yT
        hturned.1 hrows
        (fkRectDevelopedReflectedEndpointLower_pos hq n).le
        hturned.2 hcolumns
    have hoffset : Even (8 * n + 2) := by
      rw [show 8 * n + 2 = 2 * (4 * n + 1) by omega]
      exact even_two_mul _
    let B := B0.translate (8 * n + 2) hoffset
    refine ⟨⟨B, ?_⟩⟩
    intro v hv
    apply fkRectQuarterTurn_reflectedUnion_evenOffset_row_bounds
      R n hn hwidth' hheight' hH (by simp; omega)
        yT.1.2.val hrows.2
    simpa [B, B0] using hv

end
end StatMech.FrontierD
