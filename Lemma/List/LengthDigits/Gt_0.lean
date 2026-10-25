import Mathlib
import sympy.Basic
import Abbrev.Analysis.Appendix_B_1.Part6
open AppendixB
open AppendixB.PosintDecimal


/--
[PosintDecimal.length_pos](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  {p:PosintDecimal} :
-- imply
  0 < p.digits.length :=
-- proof
  AppendixB.PosintDecimal.length_pos p


-- created on 2026-10-22
