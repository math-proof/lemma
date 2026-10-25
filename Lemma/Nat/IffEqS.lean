import Mathlib
import sympy.Basic
import Abbrev.Analysis.Appendix_B_1.Part6
open AppendixB
open AppendixB.Digit


/--
[Digit.inj](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  {d d':Digit} :
-- imply
  d = d' ↔ (d:ℕ) = d' :=
-- proof
  AppendixB.Digit.inj d d'


-- created on 2026-10-22
