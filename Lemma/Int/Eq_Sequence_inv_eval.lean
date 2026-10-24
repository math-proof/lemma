import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_1
open Chapter6
open Chapter6.Sequence


/--
[Sequence.inv_eval](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a: Sequence}
  {n:ℤ} :
-- imply
  (a⁻¹) n = (a n)⁻¹ :=
-- proof
  Chapter6.Sequence.inv_eval n


-- created on 2026-10-22
