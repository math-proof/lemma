import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.Orientation.Part2
open StatMech StatMech.Onsager StatMech.Onsager.Orientation


/--
[leftCell_eq_of_leftTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Orientation.lean)
-/
@[path]
private lemma leftCell_eq_of_leftTurn_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hturn : d (k + 1) - d k = 1) :
-- imply
  leftCell (d k) (pos d k) = leftCell (d (k + 1)) (pos d (k + 1)) := by
-- proof
  apply StatMech.Onsager.Orientation.leftCell_eq_of_leftTurn d hclosed k hturn

/--
[no_vEdge_of_not_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Orientation.lean)
-/
@[path]
private lemma no_vEdge_of_not_vertex_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (c h : ℤ)
  (hnv : ∀ k : Fin n, pos d k ≠ (c, h)) :
-- imply
  ∀ k : Fin n, isVertEdge (d k) → (pos d k).1 = c → ¬ (min ((pos d k).2) ((pos d (k + 1)).2) ≤ h ∧ h < max ((pos d k).2) ((pos d (k + 1)).2)) := by
-- proof
  apply StatMech.Onsager.Orientation.no_vEdge_of_not_vertex d hclosed c h hnv

/--
[no_hEdge_of_not_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Orientation.lean)
-/
@[path]
private lemma no_hEdge_of_not_vertex_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (c h : ℤ)
  (hnv : ∀ k : Fin n, pos d k ≠ (c, h)) :
-- imply
  ∀ k : Fin n, isHorizEdge (d k) → min ((pos d k).1) ((pos d (k + 1)).1) = c → (pos d k).2 ≠ h := by
-- proof
  apply StatMech.Onsager.Orientation.no_hEdge_of_not_vertex d hclosed c h hnv

/--
[vEdge_lower_index](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Orientation.lean)
-/
@[path]
private lemma vEdge_lower_index_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {m : Fin n}
  {j : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (c h : ℤ)
  (hpm : pos d m = (c, h))
  (hvj : isVertEdge (d j))
  (hxj : (pos d j).1 = c)
  (hstraddle : min ((pos d j).2) ((pos d (j + 1)).2) ≤ h ∧ h < max ((pos d j).2) ((pos d (j + 1)).2)) :
-- imply
  j = m ∨ j + 1 = m := by
-- proof
  apply StatMech.Onsager.Orientation.vEdge_lower_index d hclosed hsimple c h m hpm j hvj hxj hstraddle

/--
[hEdge_left_index](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Orientation.lean)
-/
@[path]
private lemma hEdge_left_index_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {m : Fin n}
  {j : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (c h : ℤ)
  (hpm : pos d m = (c, h))
  (hhj : isHorizEdge (d j))
  (hxj : min ((pos d j).1) ((pos d (j + 1)).1) = c)
  (hyj : (pos d j).2 = h) :
-- imply
  j = m ∨ j + 1 = m := by
-- proof
  apply StatMech.Onsager.Orientation.hEdge_left_index d hclosed hsimple c h m hpm j hhj hxj hyj

/--
[vEdge_upper_index](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Orientation.lean)
-/
@[path]
private lemma vEdge_upper_index_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {m : Fin n}
  {j : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (c h : ℤ)
  (hpm : pos d m = (c, h + 1))
  (hvj : isVertEdge (d j))
  (hxj : (pos d j).1 = c)
  (hstraddle : min ((pos d j).2) ((pos d (j + 1)).2) ≤ h ∧ h < max ((pos d j).2) ((pos d (j + 1)).2)) :
-- imply
  j = m ∨ j + 1 = m := by
-- proof
  apply StatMech.Onsager.Orientation.vEdge_upper_index d hclosed hsimple c h m hpm j hvj hxj hstraddle

/--
[hEdge_right_index](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Orientation.lean)
-/
@[path]
private lemma hEdge_right_index_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {m : Fin n}
  {j : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (c h : ℤ)
  (hpm : pos d m = (c + 1, h))
  (hhj : isHorizEdge (d j))
  (hxj : min ((pos d j).1) ((pos d (j + 1)).1) = c)
  (hyj : (pos d j).2 = h) :
-- imply
  j = m ∨ j + 1 = m := by
-- proof
  apply StatMech.Onsager.Orientation.hEdge_right_index d hclosed hsimple c h m hpm j hhj hxj hyj

/--
[leftCell_parity_eq_of_straight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Orientation.lean)
-/
@[path]
private lemma leftCell_parity_eq_of_straight_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hst : d (k + 1) = d k) :
-- imply
  rayParity d (leftCell (d k) (pos d k)).1 (leftCell (d k) (pos d k)).2 = rayParity d (leftCell (d (k + 1)) (pos d (k + 1))).1 (leftCell (d (k + 1)) (pos d (k + 1))).2 := by
-- proof
  apply StatMech.Onsager.Orientation.leftCell_parity_eq_of_straight d hclosed hsimple k hst

/--
[leftParity_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Orientation.lean)
-/
@[path]
private lemma leftParity_step_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  leftParity d k = leftParity d (k + 1) := by
-- proof
  apply StatMech.Onsager.Orientation.leftParity_step d hclosed hsimple hreflexfree k

/--
[leftParity_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Orientation.lean)
-/
@[path]
private lemma leftParity_const_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  leftParity d k = leftParity d 0 := by
-- proof
  apply StatMech.Onsager.Orientation.leftParity_const d hclosed hsimple hreflexfree k


-- created on 2026-10-23
