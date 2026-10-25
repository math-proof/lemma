import Mathlib
import sympy.Basic
import Def.Analysis.Section_4_2.Part2
open Section_4_2 hiding Rat
open Section_4_2.Rat


/--
[Rat.eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_2.lean)
-/
@[path]
private lemma main
  {a c b d : ℤ}
-- given
  (hb: b ≠ 0)
  (hd: d ≠ 0) :
-- imply
  a // b = c // d ↔ a * d = c * b :=
-- proof
  Section_4_2.Rat.eq a c hb hd


-- created on 2026-10-22
