import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_3
open Real
open Chapter7
open Chapter7.Series


/--
[Series.zeta_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_3.lean)
-/
@[path]
private lemma main
  {q:ℝ}
-- given
  (hq: q > 1) :
-- imply
  (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ q : Series).sum = riemannZeta q :=
-- proof
  Chapter7.Series.zeta_eq hq


-- created on 2026-10-22
