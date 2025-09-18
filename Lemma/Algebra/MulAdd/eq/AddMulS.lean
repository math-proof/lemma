import Lemma.Basic


@[main, comm]
private lemma main
  [Mul α] [Add α] [RightDistribClass α]
-- given
  (a b c : α) :
-- imply
  (a + b) * c = a * c + b * c :=
-- proof
  right_distrib a b c


-- created on 2024-07-01
-- updated on 2025-07-15
