import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordSplit.Part3
open StatMech StatMech.FrontierA


/--
[kwChordPrefixIndex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean)
-/
@[path]
private lemma kwChordPrefixIndex_injective_eq
  {n : ℕ}
  [NeZero n]
  {j : Fin n} :
-- imply
  Function.Injective (kwChordPrefixIndex j) := by
-- proof
  apply StatMech.FrontierA.kwChordPrefixIndex_injective j

/--
[kwChordPrefixIndex_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean)
-/
@[path]
private lemma kwChordPrefixIndex_zero_eq
  {n : ℕ}
  [NeZero n]
  {j : Fin n} :
-- imply
  kwChordPrefixIndex j 0 = 0 := by
-- proof
  apply StatMech.FrontierA.kwChordPrefixIndex_zero j

/--
[kwChordPrefixIndex_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean)
-/
@[path]
private lemma kwChordPrefixIndex_last_eq
  {n : ℕ}
  [NeZero n]
  {j : Fin n} :
-- imply
  kwChordPrefixIndex j (Fin.last j.val) = j := by
-- proof
  apply StatMech.FrontierA.kwChordPrefixIndex_last j

/--
[kwChordPrefixIndex_castSucc_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean)
-/
@[path]
private lemma kwChordPrefixIndex_castSucc_add_one_eq
  {n : ℕ}
  [NeZero n]
  {j : Fin n}
  {q : Fin j.val} :
-- imply
  kwChordPrefixIndex j (q.castSucc + 1) = kwChordPrefixIndex j q.castSucc + 1 := by
-- proof
  apply StatMech.FrontierA.kwChordPrefixIndex_castSucc_add_one j q

/--
[kwChordPrefixIndex_last_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean)
-/
@[path]
private lemma kwChordPrefixIndex_last_add_one_eq
  {n : ℕ}
  [NeZero n]
  {j : Fin n} :
-- imply
  kwChordPrefixIndex j (Fin.last j.val + 1) = 0 := by
-- proof
  apply StatMech.FrontierA.kwChordPrefixIndex_last_add_one j

/--
[KWFiniteSimplePolygon.prefixOfCleanChord_edgeVector_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean)
-/
@[path]
private lemma prefixOfCleanChord_edgeVector_castSucc_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {j : Fin n}
  {q : Fin j.val}
-- given
  (hj : 2 ≤ j.val)
  (hclean : polygon.ChordIsClean 0 j) :
-- imply
  (polygon.prefixOfCleanChord j hj hclean).edgeVector q.castSucc = polygon.edgeVector (kwChordPrefixIndex j q.castSucc) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.prefixOfCleanChord_edgeVector_castSucc polygon j hj hclean q

/--
[KWFiniteSimplePolygon.prefixOfCleanChord_edgeVector_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean)
-/
@[path]
private lemma prefixOfCleanChord_edgeVector_last_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {j : Fin n}
-- given
  (hj : 2 ≤ j.val)
  (hclean : polygon.ChordIsClean 0 j) :
-- imply
  (polygon.prefixOfCleanChord j hj hclean).edgeVector (Fin.last j.val) = polygon.vertex 0 - polygon.vertex j := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.prefixOfCleanChord_edgeVector_last polygon j hj hclean

/--
[KWFiniteSimplePolygon.prefixOfCleanChord_edgeList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean)
-/
@[path]
private lemma prefixOfCleanChord_edgeList_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {j : Fin n}
-- given
  (hj : 2 ≤ j.val)
  (hclean : polygon.ChordIsClean 0 j) :
-- imply
  (polygon.prefixOfCleanChord j hj hclean).edgeList = (List.ofFn (fun q : Fin j.val ↦ polygon.edgeVector (kwChordPrefixIndex j q.castSucc))).concat (polygon.vertex 0 - polygon.vertex j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.prefixOfCleanChord_edgeList polygon j hj hclean

/--
[KWFiniteSimplePolygon.rotate_chordIsClean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean)
-/
@[path]
private lemma rotate_chordIsClean_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i j : Fin n}
  {r : Fin n}
-- given
  (hclean : polygon.ChordIsClean i j) :
-- imply
  (polygon.rotate r).ChordIsClean (i - r) (j - r) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.rotate_chordIsClean polygon hclean r

/--
[KWFiniteSimplePolygon.rotate_chordIsClean_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean)
-/
@[path]
private lemma rotate_chordIsClean_zero_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i j : Fin n}
-- given
  (hclean : polygon.ChordIsClean i j) :
-- imply
  (polygon.rotate i).ChordIsClean 0 (j - i) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.rotate_chordIsClean_zero polygon hclean

/--
[KWFiniteSimplePolygon.cleanChord_distance_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean)
-/
@[path]
private lemma cleanChord_distance_bounds_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i j : Fin n}
-- given
  (hij : i ≠ j)
  (hforward : j ≠ i + 1)
  (hbackward : i ≠ j + 1) :
-- imply
  let d := j - i 2 ≤ d.val ∧ d.val + 2 ≤ n := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.cleanChord_distance_bounds polygon hij hforward hbackward

/--
[KWFiniteSimplePolygon.cleanChord_two_sided_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean)
-/
@[path]
private lemma cleanChord_two_sided_bounds_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i j : Fin n}
-- given
  (hclean : polygon.ChordIsClean i j)
  (hij : i ≠ j)
  (hforward : j ≠ i + 1)
  (hbackward : i ≠ j + 1) :
-- imply
  (2 ≤ (j - i).val ∧ (j - i).val + 2 ≤ n) ∧ (2 ≤ (i - j).val ∧ (i - j).val + 2 ≤ n) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.cleanChord_two_sided_bounds polygon hclean hij hforward hbackward

/--
[KWFiniteSimplePolygon.firstOfCleanChord_card_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean)
-/
@[path]
private lemma firstOfCleanChord_card_lt_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i j : Fin n}
-- given
  (hclean : polygon.ChordIsClean i j)
  (hij : i ≠ j)
  (hforward : j ≠ i + 1)
  (hbackward : i ≠ j + 1) :
-- imply
  (j - i).val + 1 < n := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.firstOfCleanChord_card_lt polygon i j hclean hij hforward hbackward

/--
[KWFiniteSimplePolygon.secondOfCleanChord_card_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean)
-/
@[path]
private lemma secondOfCleanChord_card_lt_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i j : Fin n}
-- given
  (hclean : polygon.ChordIsClean i j)
  (hij : i ≠ j)
  (hforward : j ≠ i + 1)
  (hbackward : i ≠ j + 1) :
-- imply
  (i - j).val + 1 < n := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.secondOfCleanChord_card_lt polygon i j hclean hij hforward hbackward

/--
[KWFiniteSimplePolygon.firstOfCleanChord_edgeList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean)
-/
@[path]
private lemma firstOfCleanChord_edgeList_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i j : Fin n}
-- given
  (hclean : polygon.ChordIsClean i j)
  (hij : i ≠ j)
  (hforward : j ≠ i + 1)
  (hbackward : i ≠ j + 1) :
-- imply
  (polygon.firstOfCleanChord i j hclean hij hforward hbackward).edgeList = (List.ofFn (fun q : Fin (j - i).val ↦ (polygon.rotate i).edgeVector (kwChordPrefixIndex (j - i) q.castSucc))).concat (polygon.vertex i - polygon.vertex j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.firstOfCleanChord_edgeList polygon i j hclean hij hforward hbackward

/--
[KWFiniteSimplePolygon.secondOfCleanChord_edgeList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean)
-/
@[path]
private lemma secondOfCleanChord_edgeList_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i j : Fin n}
-- given
  (hclean : polygon.ChordIsClean i j)
  (hij : i ≠ j)
  (hforward : j ≠ i + 1)
  (hbackward : i ≠ j + 1) :
-- imply
  (polygon.secondOfCleanChord i j hclean hij hforward hbackward).edgeList = (List.ofFn (fun q : Fin (i - j).val ↦ (polygon.rotate j).edgeVector (kwChordPrefixIndex (i - j) q.castSucc))).concat (polygon.vertex j - polygon.vertex i) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.secondOfCleanChord_edgeList polygon i j hclean hij hforward hbackward


-- created on 2026-10-23
