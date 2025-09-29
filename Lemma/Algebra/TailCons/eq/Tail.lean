import stdlib.List.Vector
import sympy.Basic


@[main]
private lemma main
  {l : List α} :
-- imply
  (a :: l.tail).tail = l.tail :=
-- proof
  rfl


@[main]
private lemma vector
-- given
  (l : List.Vector α n)
  (a : α):
-- imply
  (a ::ᵥ l.tail).tail = l.tail :=
-- proof
  rfl

-- created on 2024-07-01
