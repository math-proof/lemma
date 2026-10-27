import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Appendix_A_2


/--
[imp_contrapositive](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_A_2.lean)
-/
@[path]
private lemma main
  {x:ℝ} :
-- imply
  (x^2 ≠ 4) → (x ≠ 2) :=
-- proof
  imp_contrapositive x


-- created on 2026-10-20
