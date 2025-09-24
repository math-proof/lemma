import Lemma.Basic


@[main]
private lemma main
-- given
  (l : List α)
  (g : β → γ)
  (f : α → β) :
-- imply
  (l.map f).map g = l.map (g ∘ f) :=
-- proof
  List.map_map g f l


-- created on 2024-07-01
-- updated on 2025-09-24
