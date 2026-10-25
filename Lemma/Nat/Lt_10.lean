import Mathlib
import sympy.Basic
import Abbrev.Analysis.Appendix_B_1.Part6
open AppendixB
open AppendixB.Digit


/--
[Digit.lt](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  {d:Digit} :
-- imply
  (d:ℕ) < 10 :=
-- proof
  AppendixB.Digit.lt d


-- created on 2026-10-22
