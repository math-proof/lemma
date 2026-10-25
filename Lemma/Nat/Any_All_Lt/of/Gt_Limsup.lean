import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_6_4.Part3
open EReal
open Chapter6
open Chapter6.Sequence


/--
[Sequence.gt_limsup_bounds](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean)
-/
@[path]
private lemma main
  {a:Sequence}
  {x:EReal}
-- given
  (h: x > a.limsup) :
-- imply
  ∃ N ≥ a.m, ∀ n ≥ N, a n < x :=
-- proof
  Chapter6.Sequence.gt_limsup_bounds h


-- created on 2026-10-22
