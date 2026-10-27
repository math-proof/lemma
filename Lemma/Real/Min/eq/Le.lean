import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_4.Part4
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.min_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean)
-/
@[path]
private lemma main
  {x y:Chapter5.Real} :
-- imply
  min x y = if x ≤ y then x else y :=
-- proof
  Chapter5.Real.min_eq x y


-- created on 2026-10-22
