import sympy.Basic


@[main]
private lemma main
-- given
  (l : List α)
  (g : β → γ)
  (f : α → β) :
-- imply
  (l.map f).map g = l.map (g ∘ f) := by
-- proof
  apply List.map_map


-- created on 2024-07-01
-- updated on 2025-09-24
