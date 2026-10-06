import Mathlib.Analysis.Normed.Group.Basic
import sympy.Basic


@[main]
private lemma main
  {α : Type*}
  [NormedAddCommGroup α]
  {x y : α}
-- given
  (h : x = y) :
-- imply
  ‖x‖ = ‖y‖ :=
-- proof
  congr_arg norm h


-- created on 2023-10-02
