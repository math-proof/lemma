import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Onsager.UmlaufsatzStrip
open StatMech StatMech.Onsager StatMech.Onsager.UmlaufsatzStrip


/--
[ymax_NW_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/UmlaufsatzStrip.lean)
-/
@[path]
private lemma ymax_NW_corner_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  ∃ M : Fin n, d (M - 1) = 1 ∧ d M = 2 ∧ (∀ j : Fin n, (pos d j).2 ≤ (pos d M).2) ∧ (∀ j : Fin n, (pos d j).2 = (pos d M).2 → (pos d j).1 ≤ (pos d M).1) := by
-- proof
  apply StatMech.Onsager.UmlaufsatzStrip.ymax_NW_corner d hclosed hreflexfree

/--
[ymin_SE_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/UmlaufsatzStrip.lean)
-/
@[path]
private lemma ymin_SE_corner_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  ∃ m : Fin n, d (m - 1) = 3 ∧ d m = 0 ∧ (∀ j : Fin n, (pos d m).2 ≤ (pos d j).2) := by
-- proof
  apply StatMech.Onsager.UmlaufsatzStrip.ymin_SE_corner d hclosed hreflexfree

/--
[nw_corner_neighbours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/UmlaufsatzStrip.lean)
-/
@[path]
private lemma nw_corner_neighbours_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {M : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hin : d (M - 1) = 1)
  (hout : d M = 2) :
-- imply
  pos d (M - 1) = pos d M + (0, -1) ∧ pos d (M + 1) = pos d M + (-1, 0) := by
-- proof
  apply StatMech.Onsager.UmlaufsatzStrip.nw_corner_neighbours d hclosed hin hout

/--
[nw_corners_distinct_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/UmlaufsatzStrip.lean)
-/
@[path]
private lemma nw_corners_distinct_pos_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i j : Fin n}
-- given
  (hsimple : Function.Injective (pos d))
  (hij : i ≠ j)
  (_hi : d i = 1)
  (_hi2 : d (i + 1) = 2)
  (_hj : d j = 1)
  (_hj2 : d (j + 1) = 2) :
-- imply
  pos d (i + 1) ≠ pos d (j + 1) := by
-- proof
  apply StatMech.Onsager.UmlaufsatzStrip.nw_corners_distinct_pos d hsimple hij _hi _hi2 _hj _hj2


-- created on 2026-10-23
