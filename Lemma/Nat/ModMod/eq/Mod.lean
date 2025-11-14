import Lemma.Nat.Mod_Mul.eq.Mod
open Nat


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (n d : Z) :
-- imply
  n % d % d = n % d := by
-- proof
  have := Mod_Mul.eq.Mod n 1 d
  simp at this
  assumption


-- created on 2025-06-16
-- updated on 2025-11-14
