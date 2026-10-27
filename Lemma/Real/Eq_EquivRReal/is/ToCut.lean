import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_epilogue.Part5
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.equivR_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_epilogue.lean)
-/
@[path]
private lemma main
  {x : Chapter5.Real}
  {y : ℝ} :
-- imply
  y = Chapter5.Real.equivR x ↔ y.toCut = x.toCut :=
-- proof
  Chapter5.Real.equivR_iff x y


-- created on 2026-10-22
