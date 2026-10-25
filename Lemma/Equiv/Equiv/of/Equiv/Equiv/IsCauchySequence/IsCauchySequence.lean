import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real
open Chapter5.Sequence


/--
[Sequence.mul_equiv](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {a b a' b':ℕ → ℚ}
-- given
  (ha : (a:Sequence).IsCauchy)
  (hb' : (b':Sequence).IsCauchy)
  (haa': Equiv a a')
  (hbb': Equiv b b') :
-- imply
  Equiv (a * b) (a' * b') :=
-- proof
  Chapter5.Sequence.mul_equiv ha hb' haa' hbb'


-- created on 2026-10-22
