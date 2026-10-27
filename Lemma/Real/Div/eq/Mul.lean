import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.div_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {x y:Chapter5.Real} :
-- imply
  x/y = x * y⁻¹ :=
-- proof
  Chapter5.Real.div_eq x y


-- created on 2026-10-22
