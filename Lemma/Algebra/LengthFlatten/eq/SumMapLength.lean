import Lemma.Basic


@[main, comm]
private lemma main
-- given
  (L : List (List α)) :
-- imply
  L.flatten.length = (L.map List.length).sum :=
-- proof
  List.length_flatten L


-- created on 2025-05-08
