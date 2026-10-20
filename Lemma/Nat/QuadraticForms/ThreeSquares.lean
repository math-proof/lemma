import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.QuadraticForms.ThreeSquares
open Nat


/--
[threeSquareRepresentationCount_eq_zero_of_mod_eight_eq_seven](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquares.lean)
-/
@[path]
private lemma threeSquareRepresentationCount_eq_zero_of_mod_eight_eq_seven_eq
  {n : ℕ}
-- given
  (hn : 0 < n)
  (h : n % 8 = 7) :
-- imply
  threeSquareRepresentationCount n = 0 := by
-- proof
  apply Nat.threeSquareRepresentationCount_eq_zero_of_mod_eight_eq_seven n hn h

/--
[threeSquareRepresentationCount_eq_threeSquareRepresentationCount_div_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquares.lean)
-/
@[path]
private lemma threeSquareRepresentationCount_eq_threeSquareRepresentationCount_div_four_eq
  {n : ℕ}
-- given
  (hn : 0 < n)
  (h : n % 4 = 0) :
-- imply
  threeSquareRepresentationCount n = threeSquareRepresentationCount (n / 4) := by
-- proof
  apply Nat.threeSquareRepresentationCount_eq_threeSquareRepresentationCount_div_four n hn h


-- created on 2026-10-20
