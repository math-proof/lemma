import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_7_3
open Real
open Chapter7
open Chapter7.Series


/--
[Series.partial_nonneg](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_3.lean)
-/
@[path]
private lemma main
  {s: Series}
  {N : ℤ}
-- given
  (hnon: s.nonneg) :
-- imply
  0 ≤ s.partial N :=
-- proof
  Chapter7.Series.partial_nonneg hnon N


-- created on 2026-10-22
