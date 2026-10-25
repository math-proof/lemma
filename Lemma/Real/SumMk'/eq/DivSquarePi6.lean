import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_7_3
open Real
open Chapter7
open Chapter7.Series


/--
[Series.Basel_problem](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_3.lean)
-/
@[path]
private lemma main
  :
-- imply
  (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ 2 : Series).sum = Real.pi ^ 2 / 6 :=
-- proof
  Chapter7.Series.Basel_problem


-- created on 2026-10-22
