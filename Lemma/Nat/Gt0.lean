import Mathlib
import sympy.Basic
import sympy.analysis.Appendix_B_1
open AppendixB
open AppendixB.PosintDecimal


/--
[PosintDecimal.pos](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  {p:PosintDecimal} :
-- imply
  0 < (p:ℕ) :=
-- proof
  AppendixB.PosintDecimal.pos p


-- created on 2026-10-22
