import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real
open Chapter5.CauchySequence


/--
[CauchySequence.coe_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {a:ℕ → ℚ}
-- given
  (ha: (a:Sequence).IsCauchy) :
-- imply
  (mk' ha).toSequence = (a:Sequence) :=
-- proof
  Chapter5.CauchySequence.coe_eq ha


-- created on 2026-10-22
