import Lemma.Bool.Imp.of.ImpEq
import sympy.Basic
open Bool


@[main]
private lemma main
  {a b : α}
  {p : α → Prop}
-- given
  (h : a = b → p b) :
-- imply
  a = b → p a := by
-- proof
  exact Imp.of.ImpEq h


-- created on 2026-10-03
