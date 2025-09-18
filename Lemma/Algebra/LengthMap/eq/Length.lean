import Lemma.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (f : α → β) :
-- imply
  (s.map f).length = s.length :=
-- proof
  List.length_map s f


-- created on 2025-06-11
