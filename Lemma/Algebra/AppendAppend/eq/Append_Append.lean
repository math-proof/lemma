import Lemma.Basic


@[main, comm]
private lemma main
-- given
  (a b c : List α) :
-- imply
  a ++ b ++ c = a ++ (b ++ c) :=
-- proof
  List.append_assoc a b c


-- created on 2025-05-17
