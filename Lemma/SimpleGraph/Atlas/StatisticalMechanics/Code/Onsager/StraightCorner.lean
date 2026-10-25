import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.StraightCorner
open StatMech StatMech.Onsager StatMech.Onsager.StraightCorner


/--
[not_isVert_of_isHoriz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/StraightCorner.lean)
-/
@[path]
private lemma not_isVert_of_isHoriz_eq
  {n : ℕ}
  [NeZero n]
  {w : Fin 4}
-- given
  (h : isHorizEdge w) :
-- imply
  ¬ isVertEdge w := by
-- proof
  apply StatMech.Onsager.StraightCorner.not_isVert_of_isHoriz h

/--
[not_isHoriz_of_isVert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/StraightCorner.lean)
-/
@[path]
private lemma not_isHoriz_of_isVert_eq
  {n : ℕ}
  [NeZero n]
  {w : Fin 4}
-- given
  (h : isVertEdge w) :
-- imply
  ¬ isHorizEdge w := by
-- proof
  apply StatMech.Onsager.StraightCorner.not_isHoriz_of_isVert h

/--
[cornerWeight_eq_zero_of_two_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/StraightCorner.lean)
-/
@[path]
private lemma cornerWeight_eq_zero_of_two_dvd_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {v : ℤ × ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hdvd : 2 ∣ cornerCount (interiorCells d hclosed) v) :
-- imply
  cornerWeight (cornerCount (interiorCells d hclosed) v) = 0 := by
-- proof
  apply StatMech.Onsager.StraightCorner.cornerWeight_eq_zero_of_two_dvd d hclosed v hdvd

/--
[cornerWeight_straight_horiz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/StraightCorner.lean)
-/
@[path]
private lemma cornerWeight_straight_horiz_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hstraight : d (i + 1) = d i)
  (hh : isHorizEdge (d i)) :
-- imply
  cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) = 0 := by
-- proof
  apply StatMech.Onsager.StraightCorner.cornerWeight_straight_horiz d hclosed hsimple i hstraight hh

/--
[cornerWeight_straight_vert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/StraightCorner.lean)
-/
@[path]
private lemma cornerWeight_straight_vert_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hstraight : d (i + 1) = d i)
  (hv : isVertEdge (d i)) :
-- imply
  cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) = 0 := by
-- proof
  apply StatMech.Onsager.StraightCorner.cornerWeight_straight_vert d hclosed hsimple i hstraight hv

/--
[cornerWeight_straight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/StraightCorner.lean)
-/
@[path]
private lemma cornerWeight_straight_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hstraight : d (i + 1) = d i) :
-- imply
  cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) = 0 := by
-- proof
  apply StatMech.Onsager.StraightCorner.cornerWeight_straight d hclosed hsimple i hstraight


-- created on 2026-10-23
