/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardVisibleDiagonal
import Def.StatisticalMechanics.Code.FrontierA.KacWardChordSplit.Part3


namespace StatMech.FrontierA

theorem KWFiniteSimplePolygon.firstOfCleanChord_card_lt
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i j : Fin n) (hclean : polygon.ChordIsClean i j)
    (hij : i ≠ j) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1) :
    (j - i).val + 1 < n := by
  have hbound := polygon.cleanChord_distance_bounds hij hforward hbackward
  omega

theorem KWFiniteSimplePolygon.secondOfCleanChord_card_lt
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i j : Fin n) (hclean : polygon.ChordIsClean i j)
    (hij : i ≠ j) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1) :
    (i - j).val + 1 < n := by
  have hbound := polygon.cleanChord_distance_bounds
    hij.symm hbackward hforward
  omega

theorem KWFiniteSimplePolygon.firstOfCleanChord_edgeList
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i j : Fin n) (hclean : polygon.ChordIsClean i j)
    (hij : i ≠ j) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1) :
    (polygon.firstOfCleanChord i j hclean hij hforward hbackward).edgeList =
      (List.ofFn (fun q : Fin (j - i).val ↦
        (polygon.rotate i).edgeVector
          (kwChordPrefixIndex (j - i) q.castSucc))).concat
        (polygon.vertex i - polygon.vertex j) := by
  let rotated := polygon.rotate i
  have hcleanZero : rotated.ChordIsClean 0 (j - i) :=
    polygon.rotate_chordIsClean_zero hclean
  have hbound := polygon.cleanChord_distance_bounds hij hforward hbackward
  change (rotated.prefixOfCleanChord (j - i) hbound.1 hcleanZero).edgeList = _
  rw [rotated.prefixOfCleanChord_edgeList]
  congr 1
  unfold rotated KWFiniteSimplePolygon.rotate
  dsimp only
  have h0 : (0 : Fin n) + i = i := by simp
  have hd : (j - i) + i = j := by abel
  rw [h0, hd]

theorem KWFiniteSimplePolygon.secondOfCleanChord_edgeList
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i j : Fin n) (hclean : polygon.ChordIsClean i j)
    (hij : i ≠ j) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1) :
    (polygon.secondOfCleanChord i j hclean hij hforward hbackward).edgeList =
      (List.ofFn (fun q : Fin (i - j).val ↦
        (polygon.rotate j).edgeVector
          (kwChordPrefixIndex (i - j) q.castSucc))).concat
        (polygon.vertex j - polygon.vertex i) := by
  let rotated := polygon.rotate j
  have hcleanZero : rotated.ChordIsClean 0 (i - j) :=
    polygon.rotate_chordIsClean_zero (polygon.chordIsClean_symm hclean)
  have hbound := polygon.cleanChord_distance_bounds
    hij.symm hbackward hforward
  change (rotated.prefixOfCleanChord (i - j) hbound.1 hcleanZero).edgeList = _
  rw [rotated.prefixOfCleanChord_edgeList]
  congr 1
  unfold rotated KWFiniteSimplePolygon.rotate
  dsimp only
  have h0 : (0 : Fin n) + j = j := by simp
  have hd : (i - j) + j = i := by abel
  rw [h0, hd]

end StatMech.FrontierA
