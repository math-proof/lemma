import sympy.Basic


@[main]
private lemma main
  {α β : Type u}
-- given
  (h : α = β) :
-- imply
  ∀ b : β, ∃ a : α, b = cast h a := by
-- proof
  intro b
  use cast h.symm b
  simp


-- created on 2025-05-22
-- updated on 2025-05-23
