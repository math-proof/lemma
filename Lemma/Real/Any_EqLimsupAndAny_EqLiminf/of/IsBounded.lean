import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_6_4.Part3
open EReal
open Chapter6
open Chapter6.Sequence


/--
[Sequence.finite_limsup_liminf_of_bounded](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean)
-/
@[path]
private lemma main
  {a:Sequence}
-- given
  (hbound: a.IsBounded) :
-- imply
  (∃ L_plus:ℝ, a.limsup = L_plus) ∧ (∃ L_minus:ℝ, a.liminf = L_minus) :=
-- proof
  Chapter6.Sequence.finite_limsup_liminf_of_bounded hbound


-- created on 2026-10-22
