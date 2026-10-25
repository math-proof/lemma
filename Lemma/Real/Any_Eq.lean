import Mathlib
import sympy.Basic
import Abbrev.Analysis.Appendix_B_2
open NNReal AppendixB.NNRealDecimal
open AppendixB
open AppendixB.RealDecimal


/--
[RealDecimal.surj](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_2.lean)
-/
@[path]
private lemma main
  {x:ℝ} :
-- imply
  ∃ d:RealDecimal, x = d :=
-- proof
  AppendixB.RealDecimal.surj x


-- created on 2026-10-22
