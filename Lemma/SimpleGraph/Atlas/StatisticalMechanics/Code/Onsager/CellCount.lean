import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.CellCount
open StatMech StatMech.Onsager StatMech.Onsager.CellCount


/--
[cornersOf_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellCount.lean)
-/
@[path]
private lemma cornersOf_card_eq
  {c : ℤ × ℤ} :
-- imply
  (cornersOf c).card = 4 := by
-- proof
  apply StatMech.Onsager.CellCount.cornersOf_card c

/--
[mem_cornersOf_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellCount.lean)
-/
@[path]
private lemma mem_cornersOf_iff_eq
  {c v : ℤ × ℤ} :
-- imply
  v ∈ cornersOf c ↔ c = v ∨ c = (v.1 - 1, v.2) ∨ c = (v.1, v.2 - 1) ∨ c = (v.1 - 1, v.2 - 1) := by
-- proof
  apply StatMech.Onsager.CellCount.mem_cornersOf_iff c v

/--
[cornerCount_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellCount.lean)
-/
@[path]
private lemma cornerCount_le_four_eq
  {S : Finset (ℤ × ℤ)}
  {v : ℤ × ℤ} :
-- imply
  cornerCount S v ≤ 4 := by
-- proof
  apply StatMech.Onsager.CellCount.cornerCount_le_four S v

/--
[sum_cornerCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellCount.lean)
-/
@[path]
private lemma sum_cornerCount_eq
  {S : Finset (ℤ × ℤ)} :
-- imply
  ∑ v ∈ cellVerts S, cornerCount S v = 4 * S.card := by
-- proof
  apply StatMech.Onsager.CellCount.sum_cornerCount S


-- created on 2026-10-23
