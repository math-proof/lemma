import Mathlib
import sympy.Basic
import Def.Analysis.Section_4_2.Part2
open Section_4_2 hiding Rat
open Section_4_2.Rat


/--
[Rat.mul_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_2.lean)
-/
@[path]
private lemma main
  {a c b d : ℤ}
-- given
  (hb: b ≠ 0)
  (hd: d ≠ 0) :
-- imply
  (a // b) * (c // d) = (a*c) // (b*d)  :=
-- proof
  Section_4_2.Rat.mul_eq a c hb hd


-- created on 2026-10-22
