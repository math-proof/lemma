import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_7_5
open Filter Real EReal
open Chapter7
open Chapter7.Series


/--
[Series.ratio_test_neg](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_5.lean)
-/
@[path]
private lemma main
  {s : Series}
-- given
  (hnon: ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : atTop.liminf (fun n ↦ ((|s.seq (n+1)| / |s.seq n|:ℝ):EReal)) > 1) :
-- imply
  s.diverges :=
-- proof
  Chapter7.Series.ratio_test_neg hnon h


-- created on 2026-10-22
