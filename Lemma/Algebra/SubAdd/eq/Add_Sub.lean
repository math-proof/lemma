import Lemma.Basic


@[main, comm]
private lemma main
  [SubNegMonoid α]
  (a b c : α) :
-- imply
  a + b - c = a + (b - c) :=
-- proof
  add_sub_assoc a b c


-- created on 2024-07-01
