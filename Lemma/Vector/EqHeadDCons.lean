import sympy.vector.vector
import sympy.Basic


@[main]
private lemma main
-- given
  (s : List.Vector α n)
  (a : α)
  (default : α) :
-- imply
  (a ::ᵥ s).headD default = a :=
-- proof
  rfl


-- created on 2024-07-01
