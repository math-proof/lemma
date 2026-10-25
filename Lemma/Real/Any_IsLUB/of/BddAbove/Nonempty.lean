import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_5.Part5
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.LUB_exist](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_5.lean)
-/
@[path]
private lemma main
  {E: Set Chapter5.Real}
-- given
  (hE: Set.Nonempty E)
  (hbound: BddAbove E) :
-- imply
  ∃ S, IsLUB E S :=
-- proof
  Chapter5.Real.LUB_exist hE hbound


-- created on 2026-10-22
