import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_6_2.Part2
open EReal


/--
[EReal.sup_of_bounded_nonempty](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_2.lean)
-/
@[path]
private lemma main
  {E: Set ℝ}
-- given
  (hbound: BddAbove E)
  (hnon: E.Nonempty) :
-- imply
  sSup ((fun (x:ℝ) ↦ (x:EReal)) '' E) = sSup E :=
-- proof
  EReal.sup_of_bounded_nonempty hbound hnon


-- created on 2026-10-22
