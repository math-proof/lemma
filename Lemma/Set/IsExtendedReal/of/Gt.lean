import sympy.Basic
import Mathlib


@[path]
private lemma main
  {x : EReal}
  {b : ℝ}
-- given
  (h : (b : EReal) < x) :
-- imply
  x ∈ Set.Ioi ⊥ :=
-- proof
  lt_trans (EReal.bot_lt_coe b) h


-- created on 2020-03-31
