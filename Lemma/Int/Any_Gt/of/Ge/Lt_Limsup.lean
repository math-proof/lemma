import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_4
open EReal
open Chapter6
open Chapter6.Sequence


/--
[Sequence.lt_limsup_bounds](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean)
-/
@[path]
private lemma main
  {a:Sequence}
  {x:EReal}
  {N:ℤ}
-- given
  (h: x < a.limsup)
  (hN: N ≥ a.m) :
-- imply
  ∃ n ≥ N, a n > x :=
-- proof
  Chapter6.Sequence.lt_limsup_bounds h hN


-- created on 2026-10-22
