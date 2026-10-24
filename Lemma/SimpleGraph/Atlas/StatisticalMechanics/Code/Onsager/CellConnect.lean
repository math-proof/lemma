import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.CellConnect
open StatMech StatMech.Onsager StatMech.Onsager.CellConnect


/--
[card_inter_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellConnect.lean)
-/
@[path]
private lemma card_inter_eq_sum_eq
  {S T : Finset (ℤ × ℤ)} :
-- imply
  ((S ∩ T).card : ℤ) = ∑ t ∈ T, (if t ∈ S then (1 : ℤ) else 0) := by
-- proof
  apply StatMech.Onsager.CellConnect.card_inter_eq_sum S T

/--
[cornerCount_BL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellConnect.lean)
-/
@[path]
private lemma cornerCount_BL_eq
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ}
-- given
  (hc : (x, y) ∉ S) :
-- imply
  (cornerCount S (x, y) : ℤ) = (if (x - 1, y) ∈ S then 1 else 0) + (if (x, y - 1) ∈ S then 1 else 0) + (if (x - 1, y - 1) ∈ S then 1 else 0) := by
-- proof
  apply StatMech.Onsager.CellConnect.cornerCount_BL S x y hc

/--
[cornerCount_BR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellConnect.lean)
-/
@[path]
private lemma cornerCount_BR_eq
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ}
-- given
  (hc : (x, y) ∉ S) :
-- imply
  (cornerCount S (x + 1, y) : ℤ) = (if (x + 1, y) ∈ S then 1 else 0) + (if (x + 1, y - 1) ∈ S then 1 else 0) + (if (x, y - 1) ∈ S then 1 else 0) := by
-- proof
  apply StatMech.Onsager.CellConnect.cornerCount_BR S x y hc

/--
[cornerCount_TL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellConnect.lean)
-/
@[path]
private lemma cornerCount_TL_eq
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ}
-- given
  (hc : (x, y) ∉ S) :
-- imply
  (cornerCount S (x, y + 1) : ℤ) = (if (x, y + 1) ∈ S then 1 else 0) + (if (x - 1, y + 1) ∈ S then 1 else 0) + (if (x - 1, y) ∈ S then 1 else 0) := by
-- proof
  apply StatMech.Onsager.CellConnect.cornerCount_TL S x y hc

/--
[cornerCount_TR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellConnect.lean)
-/
@[path]
private lemma cornerCount_TR_eq
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ}
-- given
  (hc : (x, y) ∉ S) :
-- imply
  (cornerCount S (x + 1, y + 1) : ℤ) = (if (x + 1, y + 1) ∈ S then 1 else 0) + (if (x, y + 1) ∈ S then 1 else 0) + (if (x + 1, y) ∈ S then 1 else 0) := by
-- proof
  apply StatMech.Onsager.CellConnect.cornerCount_TR S x y hc


-- created on 2026-10-23
