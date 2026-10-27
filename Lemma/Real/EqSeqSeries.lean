import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_7_2.Part5
open Chapter7


/--
[eval_coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_2.lean)
-/
@[path]
private lemma main
  {a: ℕ → ℝ}
  {n: ℕ} :
-- imply
  (a: Series).seq n = a n :=
-- proof
  Chapter7.Series.eval_coe a n


-- created on 2026-10-20
