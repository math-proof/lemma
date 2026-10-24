import Mathlib
import sympy.Basic
import sympy.analysis.Appendix_B_1
open AppendixB
open AppendixB.PosintDecimal


/--
[PosintDecimal.carry_zero](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  {p q:PosintDecimal} :
-- imply
  p.carry q 0 = 0 :=
-- proof
  AppendixB.PosintDecimal.carry_zero p q


-- created on 2026-10-22
