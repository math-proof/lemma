import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.PinchFree
open StatMech StatMech.Onsager StatMech.Onsager.PinchFree


/--
[straddle_nonempty_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PinchFree.lean)
-/
@[path]
private lemma straddle_nonempty_of_ne_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (h : rayParity d a b ≠ rayParity d (a + 1) b) :
-- imply
  (straddleSet d a b).Nonempty := by
-- proof
  apply StatMech.Onsager.PinchFree.straddle_nonempty_of_ne d hclosed a b h

/--
[mid_nonempty_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PinchFree.lean)
-/
@[path]
private lemma mid_nonempty_of_ne_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
-- given
  (h : rayParity d a b ≠ rayParity d a (b + 1)) :
-- imply
  (midSet d a (b + 1)).Nonempty := by
-- proof
  apply StatMech.Onsager.PinchFree.mid_nonempty_of_ne d a b h

/--
[pinch_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PinchFree.lean)
-/
@[path]
private lemma pinch_free_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {v : ℤ × ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n) :
-- imply
  ¬ pinchAt (interiorCells d hclosed) v := by
-- proof
  apply StatMech.Onsager.PinchFree.pinch_free d hclosed hsimple hn v

/--
[pinchCount_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PinchFree.lean)
-/
@[path]
private lemma pinchCount_eq_zero_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n) :
-- imply
  pinchCount (interiorCells d hclosed) = 0 := by
-- proof
  apply StatMech.Onsager.PinchFree.pinchCount_eq_zero d hclosed hsimple hn


-- created on 2026-10-23
