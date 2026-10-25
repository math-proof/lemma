import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.UmlaufsatzFinal
open StatMech StatMech.Onsager StatMech.Onsager.UmlaufsatzFinal


/--
[leftCell_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/UmlaufsatzFinal.lean)
-/
@[path]
private lemma leftCell_bridge_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {k : Fin (m + 3)} :
-- imply
  Orientation.leftCell (d k) (pos d k) = WalkCellBoundary.leftCell d k := by
-- proof
  apply StatMech.Onsager.UmlaufsatzFinal.leftCell_bridge d k

/--
[leftParity_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/UmlaufsatzFinal.lean)
-/
@[path]
private lemma leftParity_zero_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  leftParity d 0 = 1 := by
-- proof
  apply StatMech.Onsager.UmlaufsatzFinal.leftParity_zero d hclosed hsimple hreflexfree

/--
[interiorCells_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/UmlaufsatzFinal.lean)
-/
@[path]
private lemma interiorCells_bridge_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  InteriorCells.interiorCells d hclosed = WalkCellRegion.interiorCells d hclosed hsimple hreflexfree := by
-- proof
  apply StatMech.Onsager.UmlaufsatzFinal.interiorCells_bridge d hclosed hsimple hreflexfree

/--
[cc_eq_four'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/UmlaufsatzFinal.lean)
-/
@[path]
private lemma cc_eq_four'_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  cc d = 4 := by
-- proof
  apply StatMech.Onsager.UmlaufsatzFinal.cc_eq_four' d hclosed hsimple hreflexfree

/--
[cc_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/UmlaufsatzFinal.lean)
-/
@[path]
private lemma cc_eq_four_eq
  {m : ℕ}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  cc d = 4 := by
-- proof
  apply StatMech.Onsager.UmlaufsatzFinal.cc_eq_four d hclosed hsimple hn hreflexfree

/--
[stepOf_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/UmlaufsatzFinal.lean)
-/
@[path]
private lemma stepOf_ne_zero_eq
  {m : ℕ}
  {w : Fin 4} :
-- imply
  stepOf w ≠ 0 := by
-- proof
  apply StatMech.Onsager.UmlaufsatzFinal.stepOf_ne_zero w

/--
[three_le_n](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/UmlaufsatzFinal.lean)
-/
@[path]
private lemma three_le_n_eq
  {m : ℕ}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  3 ≤ n := by
-- proof
  apply StatMech.Onsager.UmlaufsatzFinal.three_le_n d hclosed hreflexfree

/--
[cc_eq_four_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/UmlaufsatzFinal.lean)
-/
@[path]
private lemma cc_eq_four_unconditional_eq
  {m : ℕ}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  cc d = 4 := by
-- proof
  apply StatMech.Onsager.UmlaufsatzFinal.cc_eq_four_unconditional d hclosed hsimple hreflexfree

/--
[hnodbl_discharged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/UmlaufsatzFinal.lean)
-/
@[path]
private lemma hnodbl_discharged_eq
  {m : ℕ}
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  Function.Injective (pos d) → cc d < 8 := by
-- proof
  apply StatMech.Onsager.UmlaufsatzFinal.hnodbl_discharged d hclosed hreflexfree


-- created on 2026-10-23
