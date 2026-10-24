import Mathlib
import sympy.Basic
import sympy.analysis.Appendix_B_1
open AppendixB
open AppendixB.PosintDecimal


/--
[PosintDecimal.eq_append](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  {p:PosintDecimal}
-- given
  (h: 2 ≤ p.digits.length) :
-- imply
  ∃ (q:PosintDecimal) (d:Digit), p = q.append d :=
-- proof
  AppendixB.PosintDecimal.eq_append h


-- created on 2026-10-22
