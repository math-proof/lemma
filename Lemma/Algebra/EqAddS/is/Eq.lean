import Lemma.Basic


/--
applicable to Nat
-/
@[main, comm, mp, mpr]
private lemma left
  [Add α]
  [IsLeftCancelAdd α]
-- given
  (a b c : α) :
-- imply
  a + b = a + c ↔ b = c :=
-- proof
  add_right_inj a


/--
applicable to Nat
-/
@[main, comm, mp, mpr]
private lemma main
  [Add α]
  [IsRightCancelAdd α]
-- given
  (a b c : α) :
-- imply
  b + a = c + a ↔ b = c :=
-- proof
  add_left_inj a


-- created on 2025-04-20
