import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[two_pow_geq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {N:ℕ} :
-- imply
  2^N ≥ N :=
-- proof
  Section_4_3.two_pow_geq N


-- created on 2026-10-20
