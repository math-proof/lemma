import sympy.Basic
import sympy.vector.vector


@[main]
private lemma main
  [Add α] [Zero α] [Mul α]
-- given
  (a a' : α)
  (s s' : List.Vector α n) :
-- imply
  (a ::ᵥ s) @ (a' ::ᵥ s') = a * a' + s @ s' :=
-- proof
  rfl


-- created on 2024-07-01
-- updated on 2026-07-10
