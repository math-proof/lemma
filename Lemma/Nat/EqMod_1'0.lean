import Lemma.Nat.Mod.eq.Sub_MulDiv
import Lemma.Nat.EqDiv_1
import Lemma.Nat.EqMul_1
import Lemma.Nat.Sub.eq.Zero
import Lemma.Nat.EqMod0_0
open Nat


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n % 1 = 0 := by
-- proof
  by_cases h : n = 0
  ·
    subst h
    apply EqMod0_0
  ·
    rw [Mod.eq.Sub_MulDiv]
    rw [EqDiv_1]
    rw [EqMul_1]
    rw [Sub.eq.Zero]


-- created on 2025-07-11
