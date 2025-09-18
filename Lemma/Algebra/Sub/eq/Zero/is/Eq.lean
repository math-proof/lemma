import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
  [AddGroup α]
-- given
  (a b : α) :
-- imply
  a - b = 0 ↔ a = b :=
-- proof
  sub_eq_zero


-- created on 2025-03-20
-- updated on 2025-08-02
