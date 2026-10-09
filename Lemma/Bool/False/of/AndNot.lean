import sympy.Basic


@[path]
private lemma main
-- given
  (h : ¬p ∧ p) :
-- imply
  False :=
-- proof
  h.left h.right


-- created on 2024-07-01
