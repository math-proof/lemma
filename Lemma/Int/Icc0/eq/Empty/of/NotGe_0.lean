import Mathlib
import sympy.Basic
import sympy.analysis.Section_8_2
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8
open Chapter8.Finset


/--
[Finset.Icc_empty](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
  {N:ℤ}
-- given
  (h: ¬ N ≥ 0) :
-- imply
  Icc 0 N = ∅ :=
-- proof
  Chapter8.Finset.Icc_empty h


-- created on 2026-10-22
