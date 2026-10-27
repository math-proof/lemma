import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9


/--
[binaryDigit_le_one](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {x : ℝ}
  {j : ℕ} :
-- imply
  binaryDigit x j ≤ 1 :=
-- proof
  binaryDigit_le_one x j


-- created on 2026-10-22
