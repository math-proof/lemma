import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_4.Part4
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.LIM_mono](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_4.lean)
-/
@[path]
private lemma main
  {a b:ℕ → ℚ}
-- given
  (ha: (a:Sequence).IsCauchy)
  (hb: (b:Sequence).IsCauchy)
  (hmono: ∀ n, a n ≤ b n) :
-- imply
  LIM a ≤ LIM b :=
-- proof
  Chapter5.Real.LIM_mono ha hb hmono


-- created on 2026-10-22
