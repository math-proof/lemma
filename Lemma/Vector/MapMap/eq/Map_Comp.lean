import sympy.Basic
import sympy.vector.Basic


@[main, comm]
private lemma main
-- given
  (l : List.Vector α n)
  (g : β → γ)
  (f : α → β) :
-- imply
  (l.map f).map g = l.map (g ∘ f) := by
-- proof
  aesop


-- created on 2025-09-24
