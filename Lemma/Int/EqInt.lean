import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_1
open Section_4_1 hiding Int
open Section_4_1.Int


/--
[Int.natCast_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_1.lean)
-/
@[path]
private lemma main
  {n:ℕ} :
-- imply
  (n:Section_4_1.Int) = n —— 0 :=
-- proof
  Section_4_1.Int.natCast_eq n


-- created on 2026-10-22
