import sympy.functions.elementary.integers
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.EqSubS.of.Eq
import Lemma.Nat.EqSubAdd
open Nat


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (n d : Z) :
-- imply
  n / d * d = n - n % d := by
-- proof
  have h := EqAddMulDiv n d
  have h := EqSubS.of.Eq h (n % d)
  rwa [EqSubAdd] at h


-- created on 2025-07-08
