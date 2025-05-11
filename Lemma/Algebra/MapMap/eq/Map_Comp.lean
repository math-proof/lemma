import Lemma.Basic


@[main]
private lemma main
-- given
  (g : β → γ)
  (f : α → β)
  (l : List α) :
-- imply
  (l.map f).map g = l.map (g ∘ f) := by
-- proof
  simp [List.map_map]


-- created on 2024-07-01
