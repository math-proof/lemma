import Lemma.Nat.Mod.eq.Sub_MulDiv
import Lemma.Nat.EqDiv_1
import Lemma.Algebra.EqMul_1
import Lemma.Nat.Sub.eq.Zero
import Lemma.Nat.Mod0.eq.Zero
open Algebra Nat


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
    apply Mod0.eq.Zero
  ·
    rw [Mod.eq.Sub_MulDiv]
    rw [EqDiv_1]
    rw [EqMul_1]
    rw [Sub.eq.Zero]


-- created on 2025-07-11
