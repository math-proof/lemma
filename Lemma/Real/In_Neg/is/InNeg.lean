import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_5.Part5
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.mem_neg](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_5.lean)
-/
@[path]
private lemma main
  {E: Set Chapter5.Real}
  {x:Chapter5.Real} :
-- imply
  x ∈ -E ↔ -x ∈ E :=
-- proof
  Chapter5.Real.mem_neg E x


-- created on 2026-10-22
