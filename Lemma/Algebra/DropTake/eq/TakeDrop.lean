import Lemma.Basic


@[main]
private lemma main
-- given
  (l : List α) 
  (i j : ℕ):
-- imply
  (l.take j).drop i = (l.drop i).take (j - i) :=
-- proof
  l.drop_take i j


-- created on 2025-06-20
