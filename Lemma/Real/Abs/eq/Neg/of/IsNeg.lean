import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_4.Part4
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.abs_of_neg](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean)
-/
@[path]
private lemma main
  {x:Chapter5.Real}
-- given
  (hx: x.IsNeg) :
-- imply
  Chapter5.Real.abs x = -x :=
-- proof
  Chapter5.Real.abs_of_neg x hx


-- created on 2026-10-22
