import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Chapter6
open Chapter6.Sequence


/--
[Sequence.sub_coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a b: ℕ → ℝ} :
-- imply
  (a:Sequence) - (b:Sequence) = (fun n ↦ a n - b n) :=
-- proof
  Chapter6.Sequence.sub_coe a b


-- created on 2026-10-22
