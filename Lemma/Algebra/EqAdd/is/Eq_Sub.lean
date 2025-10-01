import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [AddGroup α]
  {a x y : α} :
-- imply
  a + x = y ↔ a = y - x := by
-- proof
  aesop


-- created on 2024-11-27
