import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.LIM_eq_LIM](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {a b:ℕ → ℚ}
-- given
  (ha: (a:Sequence).IsCauchy)
  (hb: (b:Sequence).IsCauchy) :
-- imply
  LIM a = LIM b ↔ Sequence.Equiv a b :=
-- proof
  Chapter5.Real.LIM_eq_LIM ha hb


-- created on 2026-10-22
