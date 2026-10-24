import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_2
open Section_4_2 hiding Rat
open Section_4_2.PreRat


/--
[PreRat.eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_2.lean)
-/
@[path]
private lemma main
  {a b c d:ℤ}
-- given
  (hb: b ≠ 0)
  (hd: d ≠ 0) :
-- imply
  (⟨ a,b,hb ⟩: PreRat) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b :=
-- proof
  Section_4_2.PreRat.eq a b c d hb hd


-- created on 2026-10-22
