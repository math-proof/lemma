import Mathlib
import sympy.Basic
import sympy.analysis.Appendix_B_1
open AppendixB
open AppendixB.PosintDecimal


/--
[PosintDecimal.congr'](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  {p q:PosintDecimal}
-- given
  (h: p.digits = q.digits) :
-- imply
  p = q :=
-- proof
  AppendixB.PosintDecimal.congr' h


-- created on 2026-10-22
