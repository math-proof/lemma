import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Real


/--
[Real.close_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {ε x y : ℝ} :
-- imply
  ε.Close x y ↔ dist x y ≤ ε :=
-- proof
  Real.close_def ε x y


-- created on 2026-10-22
