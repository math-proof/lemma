import sympy.functions.elementary.exponential


@[path]
private lemma main
  [ExpPos α]
-- given
  (x : α) :
-- imply
  exp x > 0 :=
-- proof
  ExpPos.exp_pos x


-- created on 2025-10-05
