import sympy.vector.vector
import sympy.Basic


@[main]
private lemma main
-- given
  (a : α)
  (l : List.Vector α n) :
-- imply
  (a ::ᵥ l.tail).tail = l.tail :=
-- proof
  rfl


-- created on 2025-10-03
