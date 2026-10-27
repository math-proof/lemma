import Instance.Data.Int.Integers
import Initialize.Tactic.Attr.Basic


@[path, comm, mp, mpr]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n isn't odd ↔ n % 2 = 0 := by
-- proof
  rw [IntegerRing.odd_iff]
  apply IntegerRing.mod_two_ne_one


-- created on 2025-08-13
