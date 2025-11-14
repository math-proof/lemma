import sympy.Basic


@[main]
private lemma main
-- given
  (g : β → γ)
  (f : α → β) :
-- imply
  g ∘ f = fun x => g (f x) := by
-- proof
  aesop


-- created on 2025-06-13
