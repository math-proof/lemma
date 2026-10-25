import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real
open Chapter5.CauchySequence


/--
[CauchySequence.coe_coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {a:ℕ → ℚ}
-- given
  (ha: (a:Sequence).IsCauchy) :
-- imply
  mk' ha = a :=
-- proof
  Chapter5.CauchySequence.coe_coe ha


-- created on 2026-10-22
