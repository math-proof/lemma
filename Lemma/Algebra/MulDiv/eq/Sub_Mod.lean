import sympy.functions.elementary.integers
import Lemma.Algebra.Eq_AddMulDiv___Mod
import Lemma.Algebra.EqSubS.of.Eq
import Lemma.Nat.EqSubAdd
open Algebra Nat


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (n d : Z) :
-- imply
  n / d * d = n - n % d := by
-- proof
  have h := Eq_AddMulDiv___Mod n d
  have h := EqSubS.of.Eq.int h (n % d)
  rw [EqSubAdd] at h
  apply Eq.symm
  assumption


-- created on 2025-07-08
