import sympy.Basic


@[main]
private lemma main
  {α β : Type u}
-- given
  (h : α = β) :
-- imply
  ∀ b : β, ∃ a : α, cast h a = b := by
-- proof
  intro b
  use cast h.symm b
  simp


-- created on 2025-06-28
