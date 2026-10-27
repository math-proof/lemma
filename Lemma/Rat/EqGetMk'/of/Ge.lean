import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_1.Part9
open Chapter5


/--
[eval_mk](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  {n n₀:ℤ}
  {a: { n // n ≥ n₀ } → ℚ}
-- given
  (h: n ≥ n₀) :
-- imply
  (Sequence.mk' n₀ a) n = a ⟨ n, h ⟩ :=
-- proof
  Chapter5.Sequence.eval_mk a h


-- created on 2026-10-20
