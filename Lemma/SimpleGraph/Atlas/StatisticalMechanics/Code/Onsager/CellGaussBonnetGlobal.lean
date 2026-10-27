import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.CellGaussBonnetGlobal
open StatMech StatMech.Onsager StatMech.Onsager.CellGaussBonnetGlobal


/--
[pinch_diff_BL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnetGlobal.lean)
-/
@[path]
private lemma pinch_diff_BL_eq
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ}
-- given
  (hc : (x, y) ∉ S) :
-- imply
  pinchW (insert (x, y) S) (x, y) - pinchW S (x, y) = (if ((x - 1, y - 1) ∈ S ∧ (x - 1, y) ∉ S ∧ (x, y - 1) ∉ S) then (1 : ℤ) else 0) - (if ((x - 1, y) ∈ S ∧ (x, y - 1) ∈ S ∧ (x - 1, y - 1) ∉ S) then (1 : ℤ) else 0) := by
-- proof
  apply StatMech.Onsager.CellGaussBonnetGlobal.pinch_diff_BL S x y hc

/--
[pinch_diff_BR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnetGlobal.lean)
-/
@[path]
private lemma pinch_diff_BR_eq
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ}
-- given
  (hc : (x, y) ∉ S) :
-- imply
  pinchW (insert (x, y) S) (x + 1, y) - pinchW S (x + 1, y) = (if ((x + 1, y - 1) ∈ S ∧ (x + 1, y) ∉ S ∧ (x, y - 1) ∉ S) then (1 : ℤ) else 0) - (if ((x + 1, y) ∈ S ∧ (x, y - 1) ∈ S ∧ (x + 1, y - 1) ∉ S) then (1 : ℤ) else 0) := by
-- proof
  apply StatMech.Onsager.CellGaussBonnetGlobal.pinch_diff_BR S x y hc

/--
[pinch_diff_TL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnetGlobal.lean)
-/
@[path]
private lemma pinch_diff_TL_eq
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ}
-- given
  (hc : (x, y) ∉ S) :
-- imply
  pinchW (insert (x, y) S) (x, y + 1) - pinchW S (x, y + 1) = (if ((x - 1, y + 1) ∈ S ∧ (x, y + 1) ∉ S ∧ (x - 1, y) ∉ S) then (1 : ℤ) else 0) - (if ((x, y + 1) ∈ S ∧ (x - 1, y) ∈ S ∧ (x - 1, y + 1) ∉ S) then (1 : ℤ) else 0) := by
-- proof
  apply StatMech.Onsager.CellGaussBonnetGlobal.pinch_diff_TL S x y hc

/--
[pinch_diff_TR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnetGlobal.lean)
-/
@[path]
private lemma pinch_diff_TR_eq
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ}
-- given
  (hc : (x, y) ∉ S) :
-- imply
  pinchW (insert (x, y) S) (x + 1, y + 1) - pinchW S (x + 1, y + 1) = (if ((x + 1, y + 1) ∈ S ∧ (x, y + 1) ∉ S ∧ (x + 1, y) ∉ S) then (1 : ℤ) else 0) - (if ((x, y + 1) ∈ S ∧ (x + 1, y) ∈ S ∧ (x + 1, y + 1) ∉ S) then (1 : ℤ) else 0) := by
-- proof
  apply StatMech.Onsager.CellGaussBonnetGlobal.pinch_diff_TR S x y hc

/--
[pinch_jump_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnetGlobal.lean)
-/
@[path]
private lemma pinch_jump_sum_eq
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ}
-- given
  (hc : (x, y) ∉ S) :
-- imply
  (∑ v ∈ cornersOf (x, y), (pinchW (insert (x, y) S) v - pinchW S v)) = pinchDelta (decide ((x + 1, y) ∈ S)) (decide ((x - 1, y) ∈ S)) (decide ((x, y + 1) ∈ S)) (decide ((x, y - 1) ∈ S)) (decide ((x + 1, y + 1) ∈ S)) (decide ((x - 1, y + 1) ∈ S)) (decide ((x + 1, y - 1) ∈ S)) (decide ((x - 1, y - 1) ∈ S)) := by
-- proof
  apply StatMech.Onsager.CellGaussBonnetGlobal.pinch_jump_sum S x y hc

/--
[cornerDiff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnetGlobal.lean)
-/
@[path]
private lemma cornerDiff_eq_eq
  {S : Finset (ℤ × ℤ)} :
-- imply
  cornerDiff S = 4 * eulerChar S + 2 * pinchCount S := by
-- proof
  apply StatMech.Onsager.CellGaussBonnetGlobal.cornerDiff_eq S


-- created on 2026-10-23
