import sympy.functions.elementary.integers
import Lemma.Nat.ModAdd_Mul.eq.Mod
import Lemma.Nat.EqMod0_0
open Nat


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n % n = 0 := by
-- proof
  have := ModAdd_Mul.eq.Mod.left 0 n 1
  simp at this
  rw [this]
  apply EqMod0_0


-- created on 2025-10-19
