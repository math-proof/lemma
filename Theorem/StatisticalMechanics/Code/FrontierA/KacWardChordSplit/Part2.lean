/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardVisibleDiagonal
import Def.StatisticalMechanics.Code.FrontierA.KacWardChordSplit.Part2


namespace StatMech.FrontierA

theorem KWFiniteSimplePolygon.prefixOfCleanChord_edgeVector_castSucc
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 2 ≤ j.val) (hclean : polygon.ChordIsClean 0 j)
    (q : Fin j.val) :
    (polygon.prefixOfCleanChord j hj hclean).edgeVector q.castSucc =
      polygon.edgeVector (kwChordPrefixIndex j q.castSucc) := by
  unfold KWFiniteSimplePolygon.edgeVector
  change polygon.vertex (kwChordPrefixIndex j (q.castSucc + 1)) -
      polygon.vertex (kwChordPrefixIndex j q.castSucc) = _
  rw [kwChordPrefixIndex_castSucc_add_one]

theorem KWFiniteSimplePolygon.prefixOfCleanChord_edgeVector_last
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 2 ≤ j.val) (hclean : polygon.ChordIsClean 0 j) :
    (polygon.prefixOfCleanChord j hj hclean).edgeVector (Fin.last j.val) =
      polygon.vertex 0 - polygon.vertex j := by
  unfold KWFiniteSimplePolygon.edgeVector
  change polygon.vertex (kwChordPrefixIndex j (Fin.last j.val + 1)) -
      polygon.vertex (kwChordPrefixIndex j (Fin.last j.val)) = _
  rw [kwChordPrefixIndex_last_add_one, kwChordPrefixIndex_last]


theorem KWFiniteSimplePolygon.prefixOfCleanChord_edgeList
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 2 ≤ j.val) (hclean : polygon.ChordIsClean 0 j) :
    (polygon.prefixOfCleanChord j hj hclean).edgeList =
      (List.ofFn (fun q : Fin j.val ↦
        polygon.edgeVector (kwChordPrefixIndex j q.castSucc))).concat
          (polygon.vertex 0 - polygon.vertex j) := by
  unfold KWFiniteSimplePolygon.edgeList
  rw [List.ofFn_succ']
  congr 1
  · congr 1
    funext q
    exact polygon.prefixOfCleanChord_edgeVector_castSucc j hj hclean q
  · exact polygon.prefixOfCleanChord_edgeVector_last j hj hclean


theorem KWFiniteSimplePolygon.rotate_chordIsClean
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {i j : Fin n} (hclean : polygon.ChordIsClean i j) (r : Fin n) :
    (polygon.rotate r).ChordIsClean (i - r) (j - r) := by
  have hi : (i - r) + r = i := by abel
  have hj : (j - r) + r = j := by abel
  constructor
  · intro k hki hkj hbetween
    have hkiOld : k + r ≠ i := by
      intro h
      apply hki
      apply add_right_cancel (b := r)
      exact h.trans hi.symm
    have hkjOld : k + r ≠ j := by
      intro h
      apply hkj
      apply add_right_cancel (b := r)
      exact h.trans hj.symm
    unfold KWFiniteSimplePolygon.rotate at hbetween
    dsimp only at hbetween
    rw [hi, hj] at hbetween
    exact hclean.1 (k + r) hkiOld hkjOld hbetween
  · intro k
    have hsucc : (k + 1) + r = (k + r) + 1 := by abel
    unfold KWFiniteSimplePolygon.rotate
    dsimp only
    rw [hi, hj, hsucc]
    exact hclean.2 (k + r)


theorem KWFiniteSimplePolygon.rotate_chordIsClean_zero
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {i j : Fin n} (hclean : polygon.ChordIsClean i j) :
    (polygon.rotate i).ChordIsClean 0 (j - i) := by
  simpa using polygon.rotate_chordIsClean hclean i


theorem KWFiniteSimplePolygon.cleanChord_distance_bounds
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {i j : Fin n} (hij : i ≠ j)
    (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1) :
    let d := j - i
    2 ≤ d.val ∧ d.val + 2 ≤ n := by
  let d := j - i
  have hn : 3 ≤ n := polygon.three_le
  have hd0 : d.val ≠ 0 := by
    intro hval
    have hd : d = 0 := by
      apply Fin.ext
      simpa using hval
    apply hij
    dsimp only [d] at hd
    apply sub_eq_zero.mp hd |>.symm
  have hd1 : d.val ≠ 1 := by
    intro hval
    have hd : d = (1 : Fin n) := by
      apply Fin.ext
      simpa [Nat.mod_eq_of_lt (by omega : 1 < n)] using hval
    apply hforward
    calc
      j = d + i := by dsimp only [d]; abel
      _ = 1 + i := by rw [hd]
      _ = i + 1 := by abel
  have hdLast : d.val ≠ n - 1 := by
    intro hval
    have hdWrap : d + 1 = 0 := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_zero]
      have hOne : (1 : Fin n).val = 1 := by
        simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
      rw [hOne]
      rw [hval]
      have hnEq : n - 1 + 1 = n := by omega
      rw [hnEq, Nat.mod_self]
    apply hbackward
    calc
      i = 0 + i := by simp
      _ = (d + 1) + i := by rw [hdWrap]
      _ = j + 1 := by dsimp only [d]; abel
  constructor <;> omega


theorem KWFiniteSimplePolygon.cleanChord_two_sided_bounds
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {i j : Fin n} (hclean : polygon.ChordIsClean i j)
    (hij : i ≠ j) (hforward : j ≠ i + 1)
    (hbackward : i ≠ j + 1) :
    (2 ≤ (j - i).val ∧ (j - i).val + 2 ≤ n) ∧
      (2 ≤ (i - j).val ∧ (i - j).val + 2 ≤ n) := by
  exact ⟨polygon.cleanChord_distance_bounds hij hforward hbackward,
    polygon.cleanChord_distance_bounds hij.symm hbackward hforward⟩


end StatMech.FrontierA
