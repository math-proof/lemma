import sympy.Basic


/--
mpr is not defined for Int, it is defined in Nat:
Nat.EqSubS.of.Eq [Sub α]
-/
@[main, comm, mp]
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
