/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/FirstDifference.lean -/

import Mathlib.Data.ZMod.Basic

/-!
# First differences of binary words

This file formalizes the first-difference operation from Ricardo Astudillo,
*On a Class of Thue-Morse Type Sequences*:
<https://cs.uwaterloo.ca/journals/JIS/VOL6/Astudillo/astudillo12.tex>.
-/

namespace MetaMathlibExt

/-- The first difference of an infinite binary word: `(Δw) i = w (i + 1) - w i`. -/
def firstDifference (w : ℕ → ZMod 2) : ℕ → ZMod 2 :=
  fun i ↦ w (i + 1) - w i

/-- The adjacent first differences of a finite binary word. -/
def firstDifferenceList (w : List (ZMod 2)) : List (ZMod 2) :=
  List.zipWith (· - ·) w.tail w

@[simp]
theorem length_firstDifferenceList (w : List (ZMod 2)) :
    (firstDifferenceList w).length = w.length - 1 := by
  cases w <;> simp [firstDifferenceList]

end MetaMathlibExt
