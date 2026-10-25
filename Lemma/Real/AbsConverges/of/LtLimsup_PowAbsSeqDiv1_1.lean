import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_7_5
open Filter Real EReal
open Chapter7
open Chapter7.Series


/--
[Series.root_test_pos](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_5.lean)
-/
@[path]
private lemma main
  {s : Series}
-- given
  (h : atTop.limsup (fun n ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ):EReal)) < 1) :
-- imply
  s.absConverges :=
-- proof
  Chapter7.Series.root_test_pos h


-- created on 2026-10-22
