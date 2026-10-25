import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
open EReal


/--
[EReal.pos_fun_smul_neg](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {f: X → ℝ}
  {c: ℝ}
-- given
  (hc: c < 0) :
-- imply
  EReal.pos_fun (c • f) = ((-c) : EReal) • EReal.neg_fun f :=
-- proof
  EReal.pos_fun_smul_neg f c hc


-- created on 2026-10-22
