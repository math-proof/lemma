import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.equational


/--
[S_left_ideal](https://github.com/teorth/analysis/blob/main/Analysis/Misc/equational.lean)
-/
@[path]
private lemma main
  [Magma M]
  {a b z : M}
-- given
  (h : Equation1689 M) :
-- imply
  S b a = a ◇ S z (S b a) :=
-- proof
  S_left_ideal h a b z


-- created on 2026-10-22
