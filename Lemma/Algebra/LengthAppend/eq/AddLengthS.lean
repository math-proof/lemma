import Lemma.Basic


@[main, comm]
private lemma main
-- given
  (a b : List α) :
-- imply
  (a ++ b).length = a.length + b.length :=
-- proof
  List.length_append a b


-- created on 2025-05-08
