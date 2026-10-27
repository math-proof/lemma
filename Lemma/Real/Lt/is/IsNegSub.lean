import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_4.Part4
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.lt_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean)
-/
@[path]
private lemma main
  {x y:Chapter5.Real} :
-- imply
  x < y ↔ (x-y).IsNeg :=
-- proof
  Chapter5.Real.lt_iff x y


-- created on 2026-10-22
