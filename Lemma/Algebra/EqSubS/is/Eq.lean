import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [AddGroup α]
-- given
  (x y d : α) :
-- imply
  x - d = y - d ↔ x = y :=
-- proof
  sub_left_inj


-- created on 2025-03-30
-- updated on 2025-06-21
