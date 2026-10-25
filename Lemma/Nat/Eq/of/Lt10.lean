import Mathlib
import sympy.Basic
import Abbrev.Analysis.Appendix_B_1.Part6
open AppendixB
open AppendixB.Digit


/--
[Digit.mk_eq_iff](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  {d:Digit}
  {n:ℕ}
-- given
  (h: n < 10) :
-- imply
  d = mk h ↔ (d:ℕ) = n :=
-- proof
  AppendixB.Digit.mk_eq_iff d h


-- created on 2026-10-22
