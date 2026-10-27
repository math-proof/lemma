import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.eq_lim](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {x:Chapter5.Real} :
-- imply
  ∃ (a:ℕ → ℚ), (a:Sequence).IsCauchy ∧ x = LIM a :=
-- proof
  Chapter5.Real.eq_lim x


-- created on 2026-10-22
