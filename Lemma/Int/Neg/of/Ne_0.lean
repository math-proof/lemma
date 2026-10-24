import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_2
open Section_4_2 hiding Rat
open Section_4_2.Rat


/--
[Rat.neg_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_2.lean)
-/
@[path]
private lemma main
  {a b : ℤ}
-- given
  (hb: b ≠ 0) :
-- imply
  - (a // b) = (-a) // b :=
-- proof
  Section_4_2.Rat.neg_eq a hb


-- created on 2026-10-22
