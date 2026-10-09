import sympy.Basic
import sympy.vector.vector


@[path]
private lemma main
  [NatCast α]
-- given
  (r : ℕ) :
-- imply
  (r : List.Vector α n) = List.Vector.replicate n (r : α) :=
-- proof
  rfl


-- created on 2026-07-08
