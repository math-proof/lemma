import Lemma.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (f : α → β) :
-- imply
  (s.map f).length = s.length := by
-- proof
  apply List.length_map


-- created on 2025-06-11
