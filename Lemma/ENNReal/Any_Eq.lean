import Mathlib
import sympy.Basic
import Abbrev.Analysis.Appendix_B_2
open NNReal AppendixB.NNRealDecimal
open AppendixB


/--
[NNRealDecimal.surj](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_2.lean)
-/
@[path]
private lemma main
  {x:NNReal} :
-- imply
  ∃ d:NNRealDecimal, x = d :=
-- proof
  AppendixB.NNRealDecimal.surj x


-- created on 2026-10-22
