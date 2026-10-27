import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_7_2.Part5
open Chapter7


/--
[add_coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_2.lean)
-/
@[path]
private lemma main
  {a b: ℕ → ℝ} :
-- imply
  (a:Series) + (b:Series) = (fun n ↦ a n + b n) :=
-- proof
  Chapter7.Series.add_coe a b


-- created on 2026-10-20
