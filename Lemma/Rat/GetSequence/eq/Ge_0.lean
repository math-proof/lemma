import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_1.Part9
open Chapter5


/--
[eval_coe_at_int](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  {n:ℤ}
  {a: ℕ → ℚ} :
-- imply
  (a:Sequence) n = if n ≥ 0 then a n.toNat else 0 :=
-- proof
  Chapter5.Sequence.eval_coe_at_int n a


-- created on 2026-10-20
