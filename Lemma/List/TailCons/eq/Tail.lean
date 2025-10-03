import sympy.vector.vector
import sympy.Basic


@[main]
private lemma main
-- given
  (l : List α)
  (a : α) :
-- imply
  (a :: l.tail).tail = l.tail :=
-- proof
rfl


-- created on 2024-07-01
-- updated on 2025-10-03
