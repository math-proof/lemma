import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_2
open Section_4_2 hiding Rat
open Section_4_2.Rat


/--
[Rat.inv_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_2.lean)
-/
@[path]
private lemma main
  {a b : ℤ}
-- given
  (hb: b ≠ 0) :
-- imply
  (a // b)⁻¹ = b // a :=
-- proof
  Section_4_2.Rat.inv_eq a hb


-- created on 2026-10-22
