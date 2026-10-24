import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_1
open Chapter6
open Chapter6.Sequence


/--
[Sequence.eval_mk](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {n m:ℤ}
  {a: { n // n ≥ m } → ℝ}
-- given
  (h: n ≥ m) :
-- imply
  (Sequence.mk' m a) n = a ⟨ n, h ⟩ :=
-- proof
  Chapter6.Sequence.eval_mk a h


-- created on 2026-10-22
