import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Chapter6
open Chapter6.Sequence


/--
[Sequence.from_eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a:Sequence}
  {m₁ n:ℤ}
-- given
  (hn: n ≥ m₁) :
-- imply
  (a.from m₁) n = a n :=
-- proof
  Chapter6.Sequence.from_eval a hn


-- created on 2026-10-22
