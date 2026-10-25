import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_4_1.Part8
open Section_4_1 hiding Int
open Section_4_1.Int


/--
[Int.natCast_inj](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_1.lean)
-/
@[path]
private lemma main
  {n m:ℕ} :
-- imply
  (n : Section_4_1.Int) = (m : Section_4_1.Int) ↔ n = m :=
-- proof
  Section_4_1.Int.natCast_inj n m


-- created on 2026-10-22
