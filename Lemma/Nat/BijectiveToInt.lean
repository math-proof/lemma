import Mathlib
import sympy.Basic
import sympy.analysis.Appendix_B_1
open AppendixB
open AppendixB.IntDecimal


/--
[IntDecimal.Int_bij](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_1.lean)
-/
@[path]
private lemma main
  :
-- imply
  Function.Bijective IntDecimal.toInt :=
-- proof
  AppendixB.IntDecimal.Int_bij


-- created on 2026-10-22
