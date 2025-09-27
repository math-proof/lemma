import Lemma.Basic


@[main, comm, mp]
private lemma main
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  ¬a > b ↔ a ≤ b :=
-- proof
  not_lt


-- created on 2025-04-18
