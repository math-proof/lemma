import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.sub_eq_add_neg](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {x y:Chapter5.Real} :
-- imply
  x - y = x + (-y) :=
-- proof
  Chapter5.Real.sub_eq_add_neg x y


-- created on 2026-10-22
