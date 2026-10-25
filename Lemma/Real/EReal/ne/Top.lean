import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_6_2.Part2
open EReal


/--
[EReal.real_neq_infty](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_2.lean)
-/
@[path]
private lemma main
  {x:ℝ} :
-- imply
  (x:EReal) ≠ ⊤ :=
-- proof
  EReal.real_neq_infty x


-- created on 2026-10-22
